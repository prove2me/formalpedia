-- Prove2me | solution 1 for SlowConvergence.Newton.slow_newton
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:48:05.719012+00:00
-- url     : https://prove2.me/submissions/b556c065-6274-4140-b187-3836af6a8fa4

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces
import Theorems.Thm_SlowConvergence_Newton_bounded_below
import Theorems.Thm_SlowConvergence_Newton_hermite_p_conditions
import Theorems.Thm_SlowConvergence_Newton_p_second_deriv_bound
import Theorems.Thm_SlowConvergence_Newton_q_interpolation
import Theorems.Thm_SlowConvergence_Newton_q_second_deriv_bound
import Theorems.Thm_SlowConvergence_Newton_psi_mem
import Theorems.Thm_SlowConvergence_Newton_newton_step_conditions
import Theorems.Thm_SlowConvergence_Newton_gradient_lower_bound

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Filter Topology Set

namespace SNGlue

noncomputable def gidx (T : ℕ → ℝ) (t : ℝ) : ℕ := by
  classical
  exact if h : ∃ k, t < T (k + 1) then Nat.find h else 0

noncomputable def glue (T : ℕ → ℝ) (Q : ℝ → ℝ) (P : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then Q t else P (gidx T t) t

lemma gidx_spec {T : ℕ → ℝ} (hT : StrictMono T) {k : ℕ} {t : ℝ} (h1 : T k ≤ t)
    (h2 : t < T (k + 1)) : gidx T t = k := by
  classical
  have h : ∃ k, t < T (k + 1) := ⟨k, h2⟩
  unfold gidx
  rw [dif_pos h]
  rw [Nat.find_eq_iff]
  refine ⟨h2, fun n hn => ?_⟩
  have : T (n + 1) ≤ T k := hT.monotone (by omega)
  linarith

lemma exists_piece {T : ℕ → ℝ} (hT0 : T 0 = 0) (hTu : ∀ x : ℝ, ∃ k, x < T (k + 1))
    {t : ℝ} (ht : 0 ≤ t) : ∃ k, T k ≤ t ∧ t < T (k + 1) := by
  classical
  refine ⟨Nat.find (hTu t), ?_, Nat.find_spec (hTu t)⟩
  rcases h : Nat.find (hTu t) with _ | j
  · rw [hT0]; exact ht
  · have := Nat.find_min (hTu t) (show j < Nat.find (hTu t) by omega)
    exact not_lt.mp this

section
variable {T : ℕ → ℝ} (hT : StrictMono T) (hT0 : T 0 = 0) {Q : ℝ → ℝ} {P : ℕ → ℝ → ℝ}
include hT hT0

lemma T_nonneg (k : ℕ) : 0 ≤ T k := by
  rw [← hT0]; exact hT.monotone (Nat.zero_le k)

lemma glue_eq_on (hm : ∀ k, P (k + 1) (T (k + 1)) = P k (T (k + 1))) (k : ℕ) {t : ℝ}
    (h1 : T k ≤ t) (h2 : t ≤ T (k + 1)) : glue T Q P t = P k t := by
  have ht : ¬ t < 0 := not_lt.mpr ((T_nonneg hT hT0 k).trans h1)
  unfold glue
  rw [if_neg ht]
  rcases h2.lt_or_eq with h | h
  · rw [gidx_spec hT h1 h]
  · subst h
    rw [gidx_spec hT le_rfl (hT (Nat.lt_succ_self _)), hm]

lemma glue_eq_neg (hQ : Q 0 = P 0 0) {t : ℝ} (ht : t ≤ 0) : glue T Q P t = Q t := by
  unfold glue
  rcases ht.lt_or_eq with h | h
  · rw [if_pos h]
  · subst h
    rw [if_neg (lt_irrefl _), gidx_spec hT (le_of_eq hT0) (by rw [← hT0]; exact hT (Nat.lt_succ_self 0)),
      hQ]

lemma glue_hasDerivAt (hTu : ∀ x : ℝ, ∃ k, x < T (k + 1))
    {Q' : ℝ → ℝ} {P' : ℕ → ℝ → ℝ}
    (hP : ∀ k t, HasDerivAt (P k) (P' k t) t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hm : ∀ k, P (k + 1) (T (k + 1)) = P k (T (k + 1))) (hQ : Q 0 = P 0 0)
    (hm' : ∀ k, P' (k + 1) (T (k + 1)) = P' k (T (k + 1))) (hQ' : Q' 0 = P' 0 0) (t : ℝ) :
    HasDerivAt (glue T Q P) (glue T Q' P' t) t := by
  rcases lt_or_ge t 0 with ht | ht
  · have e : glue T Q P =ᶠ[𝓝 t] Q := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [glue, show s < 0 from hs]
    rw [show glue T Q' P' t = Q' t by simp [glue, ht]]
    exact (hQd t).congr_of_eventuallyEq e
  · obtain ⟨k, hk1, hk2⟩ := exists_piece hT0 hTu ht
    rw [glue_eq_on hT hT0 hm' k hk1 hk2.le]
    have hr : HasDerivWithinAt (glue T Q P) (P' k t) (Ici t) t := by
      apply (hP k t).hasDerivWithinAt.congr_of_eventuallyEq
      · filter_upwards [Icc_mem_nhdsGE hk2] with s hs
        exact glue_eq_on hT hT0 hm k (hk1.trans hs.1) hs.2
      · exact glue_eq_on hT hT0 hm k hk1 hk2.le
    have hl : HasDerivWithinAt (glue T Q P) (P' k t) (Iic t) t := by
      rcases hk1.lt_or_eq with hlt | heq
      · apply (hP k t).hasDerivWithinAt.congr_of_eventuallyEq
        · filter_upwards [Icc_mem_nhdsLE hlt] with s hs
          exact glue_eq_on hT hT0 hm k hs.1 (hs.2.trans hk2.le)
        · exact glue_eq_on hT hT0 hm k hk1 hk2.le
      · cases k with
        | zero =>
          have h0 : t = 0 := by rw [← heq, hT0]
          subst h0
          rw [← hQ']
          apply (hQd 0).hasDerivWithinAt.congr_of_eventuallyEq
          · filter_upwards [Icc_mem_nhdsLE (show (-1 : ℝ) < 0 by norm_num)] with s hs
            exact glue_eq_neg hT hT0 hQ hs.2
          · exact glue_eq_neg hT hT0 hQ le_rfl
        | succ j =>
          subst heq
          rw [hm' j]
          apply (hP j (T (j + 1))).hasDerivWithinAt.congr_of_eventuallyEq
          · filter_upwards [Icc_mem_nhdsLE (hT (Nat.lt_succ_self j))] with s hs
            exact glue_eq_on hT hT0 hm j hs.1 hs.2
          · exact glue_eq_on hT hT0 hm j (hT (Nat.lt_succ_self j)).le le_rfl
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

lemma glue_continuous (hTu : ∀ x : ℝ, ∃ k, x < T (k + 1))
    (hP : ∀ k, Continuous (P k)) (hQc : Continuous Q)
    (hm : ∀ k, P (k + 1) (T (k + 1)) = P k (T (k + 1))) (hQ : Q 0 = P 0 0) :
    Continuous (glue T Q P) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have e : glue T Q P =ᶠ[𝓝 t] Q := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [glue, show s < 0 from hs]
    exact (hQc.continuousAt).congr_of_eventuallyEq e
  · obtain ⟨k, hk1, hk2⟩ := exists_piece hT0 hTu ht
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · rcases hk1.lt_or_eq with hlt | heq
      · apply ((hP k).continuousAt.continuousWithinAt).congr_of_eventuallyEq
        · filter_upwards [Icc_mem_nhdsLE hlt] with s hs
          exact glue_eq_on hT hT0 hm k hs.1 (hs.2.trans hk2.le)
        · exact glue_eq_on hT hT0 hm k hk1 hk2.le
      · cases k with
        | zero =>
          have h0 : t = 0 := by rw [← heq, hT0]
          subst h0
          apply (hQc.continuousAt.continuousWithinAt).congr_of_eventuallyEq
          · filter_upwards [Icc_mem_nhdsLE (show (-1 : ℝ) < 0 by norm_num)] with s hs
            exact glue_eq_neg hT hT0 hQ hs.2
          · exact glue_eq_neg hT hT0 hQ le_rfl
        | succ j =>
          subst heq
          apply ((hP j).continuousAt.continuousWithinAt).congr_of_eventuallyEq
          · filter_upwards [Icc_mem_nhdsLE (hT (Nat.lt_succ_self j))] with s hs
            exact glue_eq_on hT hT0 hm j hs.1 hs.2
          · exact glue_eq_on hT hT0 hm j (hT (Nat.lt_succ_self j)).le le_rfl
    · apply ((hP k).continuousAt.continuousWithinAt).congr_of_eventuallyEq
      · filter_upwards [Icc_mem_nhdsGE hk2] with s hs
        exact glue_eq_on hT hT0 hm k (hk1.trans hs.1) hs.2
      · exact glue_eq_on hT hT0 hm k hk1 hk2.le

end

end SNGlue



open Filter Topology Set

namespace SNGlue

def quint (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  a 0 + a 1 * u + a 2 * u ^ 2 + a 3 * u ^ 3 + a 4 * u ^ 4 + a 5 * u ^ 5

def D (a : ℕ → ℝ) : ℕ → ℝ := fun i => if i < 5 then ((i : ℝ) + 1) * a (i + 1) else 0

def trunc2 (a : ℕ → ℝ) : ℕ → ℝ := fun i => if i ≤ 2 then a i else 0

lemma hasDerivAt_quint (a : ℕ → ℝ) (u : ℝ) : HasDerivAt (quint a) (quint (D a) u) u := by
  have h := ((((((hasDerivAt_const u (a 0)).add ((hasDerivAt_id u).const_mul (a 1))).add
    ((hasDerivAt_pow 2 u).const_mul (a 2))).add ((hasDerivAt_pow 3 u).const_mul (a 3))).add
    ((hasDerivAt_pow 4 u).const_mul (a 4))).add ((hasDerivAt_pow 5 u).const_mul (a 5)))
  have e : quint a = fun u => a 0 + a 1 * id u + a 2 * u ^ 2 + a 3 * u ^ 3 + a 4 * u ^ 4
      + a 5 * u ^ 5 := by funext u; rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold quint D
  norm_num
  ring

lemma continuous_quint (a : ℕ → ℝ) : Continuous (quint a) := by
  unfold quint; fun_prop

/-- spline pieces in absolute coordinates -/
def piece (T : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (k : ℕ) (t : ℝ) : ℝ := quint (c k) (t - T k)

noncomputable def S0 (T : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : ℝ → ℝ :=
  glue T (quint (trunc2 (c 0))) (piece T c)
noncomputable def S1 (T : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : ℝ → ℝ :=
  glue T (quint (D (trunc2 (c 0)))) (piece T (fun k => D (c k)))
noncomputable def S2 (T : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : ℝ → ℝ :=
  glue T (quint (D (D (trunc2 (c 0))))) (piece T (fun k => D (D (c k))))

lemma hasDerivAt_piece (T : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (piece T c k) (piece T (fun k => D (c k)) k t) t := by
  unfold piece
  exact HasDerivAt.comp_sub_const t (T k) (hasDerivAt_quint (c k) (t - T k))

/-- matching of a coefficient family at the knots -/
def Match (T : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : Prop :=
  ∀ k, quint (c (k + 1)) 0 = quint (c k) (T (k + 1) - T k)

lemma match_piece {T : ℕ → ℝ} {c : ℕ → ℕ → ℝ} (h : Match T c) (k : ℕ) :
    piece T c (k + 1) (T (k + 1)) = piece T c k (T (k + 1)) := by
  unfold piece; rw [sub_self]; exact h k

section
variable {T : ℕ → ℝ} (hT : StrictMono T) (hT0 : T 0 = 0) (hTu : ∀ x : ℝ, ∃ k, x < T (k + 1))
  {c : ℕ → ℕ → ℝ} (h0 : Match T c) (h1 : Match T (fun k => D (c k)))
  (h2 : Match T (fun k => D (D (c k))))
include hT hT0 hTu h0 h1 h2

lemma S0_hasDerivAt (t : ℝ) : HasDerivAt (S0 T c) (S1 T c t) t := by
  apply glue_hasDerivAt hT hT0 hTu (hasDerivAt_piece T c) (hasDerivAt_quint _) (match_piece h0)
  · simp [piece, hT0, quint, trunc2]
  · exact match_piece h1
  · simp [piece, hT0, quint, trunc2, D]

lemma S1_hasDerivAt (t : ℝ) : HasDerivAt (S1 T c) (S2 T c t) t := by
  apply glue_hasDerivAt hT hT0 hTu (hasDerivAt_piece T _) (hasDerivAt_quint _) (match_piece h1)
  · simp [piece, hT0, quint, trunc2, D]
  · exact match_piece h2
  · simp [piece, hT0, quint, trunc2, D]

lemma S2_continuous : Continuous (S2 T c) := by
  apply glue_continuous hT hT0 hTu (fun k => ?_) (continuous_quint _) (match_piece h2)
  · simp [piece, hT0, quint, trunc2, D]
  · unfold piece; exact (continuous_quint _).comp (continuous_id.sub continuous_const)

lemma S0_contDiff : ContDiff ℝ 2 (S0 T c) := by
  have d0 : deriv (S0 T c) = S1 T c := funext fun t => (S0_hasDerivAt hT hT0 hTu h0 h1 h2 t).deriv
  have d1 : deriv (S1 T c) = S2 T c := funext fun t => (S1_hasDerivAt hT hT0 hTu h0 h1 h2 t).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t => (S0_hasDerivAt hT hT0 hTu h0 h1 h2 t).differentiableAt, by simp, ?_⟩
  rw [d0, contDiff_one_iff_deriv, d1]
  exact ⟨fun t => (S1_hasDerivAt hT hT0 hTu h0 h1 h2 t).differentiableAt,
    S2_continuous hT hT0 hTu h0 h1 h2⟩

end

end SNGlue



open Filter Topology Set SNGlue SlowConvergence.Newton

namespace SNOneD

lemma eta_pos {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) : 0 < eta τ := by
  unfold eta; apply div_pos h0; linarith

lemma eta_lt {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) : eta τ < 1 / 2 := by
  unfold eta; rw [div_lt_iff₀ (by linarith)]; linarith

lemma mu_pos (τ : ℝ) (k : ℕ) : 0 < mu τ k := by
  unfold mu; exact Real.rpow_pos_of_pos (by positivity) _

lemma mu_succ (τ : ℝ) (k : ℕ) : mu τ (k + 1) = (1 / ((k : ℝ) + 2)) ^ (1 / 2 + eta τ) := by
  unfold mu; push_cast; ring_nf

lemma mu_ge {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ mu τ k := by
  unfold mu
  have hb : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have := Real.rpow_le_rpow_of_exponent_ge (x := 1 / ((k : ℝ) + 1)) (by positivity) hb
    (show 1 / 2 + eta τ ≤ 1 by linarith [eta_lt h0 h1])
  simpa using this

lemma mu_le_one {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (k : ℕ) : mu τ k ≤ 1 := by
  unfold mu
  have hb : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  exact Real.rpow_le_one (by positivity) hb (by linarith [eta_pos h0 h1])

/-- knots of the first coordinate: `[x_k]_1 = ∑_{j<k} µ_j` -/
noncomputable def T1 (τ : ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, mu τ j

noncomputable def T2 (k : ℕ) : ℝ := (k : ℝ)

lemma T1_mono (τ : ℝ) : StrictMono (T1 τ) := by
  apply strictMono_nat_of_lt_succ
  intro k; unfold T1; rw [Finset.sum_range_succ]; linarith [mu_pos τ k]

lemma T1_zero (τ : ℝ) : T1 τ 0 = 0 := by simp [T1]

lemma T1_succ (τ : ℝ) (k : ℕ) : T1 τ (k + 1) - T1 τ k = mu τ k := by
  unfold T1; rw [Finset.sum_range_succ]; ring

lemma T1_unbounded {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (x : ℝ) : ∃ k, x < T1 τ (k + 1) := by
  obtain ⟨n, hn⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop x).exists
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  have : ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ≤ T1 τ n :=
    Finset.sum_le_sum (fun i _ => mu_ge h0 h1 i)
  exact this.trans (T1_mono τ (Nat.lt_succ_self n)).le

lemma T2_mono : StrictMono T2 := by
  intro a b h; unfold T2; exact_mod_cast h

lemma T2_zero : T2 0 = 0 := by simp [T2]

lemma T2_unbounded (x : ℝ) : ∃ k, x < T2 (k + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact ⟨n, by unfold T2; push_cast; linarith⟩

/-- coefficients of the first-coordinate pieces -/
noncomputable def cA (τ : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ) + f21knot τ (k + 1)
  | 1 => -mu τ k
  | 2 => 1 / 2
  | 3 => -4 * phi τ k / mu τ k
  | 4 => 7 * phi τ k / mu τ k ^ 2
  | 5 => -3 * phi τ k / mu τ k ^ 3
  | _ => 0

noncomputable def cB (k : ℕ) : ℕ → ℝ
  | 0 => 1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2 + f22knot (k + 1)
  | 1 => -((1 / ((k : ℝ) + 1)) ^ 2)
  | 2 => 1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2
  | 3 => 1 / 2 * (9 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2)
  | 4 => 1 / 2 * (-16 * (1 / ((k : ℝ) + 2)) ^ 2 + 2 * (1 / ((k : ℝ) + 1)) ^ 2)
  | 5 => 1 / 2 * (7 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2)
  | _ => 0

lemma quint_cA (τ : ℝ) (k : ℕ) (u : ℝ) : quint (cA τ k) u = p τ k u + f21knot τ (k + 1) := by
  simp only [quint, cA, p]; ring

lemma quint_cB (k : ℕ) (u : ℝ) : quint (cB k) u = q k u + f22knot (k + 1) := by
  simp only [quint, cB, q]; ring

lemma deriv_p (τ : ℝ) (k : ℕ) : deriv (p τ k) = quint (D (cA τ k)) := by
  funext u
  have e : p τ k = fun u => quint (cA τ k) u - f21knot τ (k + 1) := by
    funext u; rw [quint_cA]; ring
  rw [e]
  exact ((hasDerivAt_quint _ u).sub_const _).deriv

lemma deriv2_p (τ : ℝ) (k : ℕ) : deriv (deriv (p τ k)) = quint (D (D (cA τ k))) := by
  rw [deriv_p]; funext u; exact (hasDerivAt_quint _ u).deriv

lemma deriv_q (k : ℕ) : deriv (q k) = quint (D (cB k)) := by
  funext u
  have e : q k = fun u => quint (cB k) u - f22knot (k + 1) := by
    funext u; rw [quint_cB]; ring
  rw [e]
  exact ((hasDerivAt_quint _ u).sub_const _).deriv

lemma deriv2_q (k : ℕ) : deriv (deriv (q k)) = quint (D (D (cB k))) := by
  rw [deriv_q]; funext u; exact (hasDerivAt_quint _ u).deriv

section
variable {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
include hτ0 hτ1

lemma matchA0 : Match (T1 τ) (cA τ) := by
  intro k
  rw [T1_succ, quint_cA τ k, (hermite_p_conditions τ hτ0 hτ1 k).2.1]
  simp only [quint, cA, f21knot]
  push_cast; ring

lemma matchA1 : Match (T1 τ) (fun k => D (cA τ k)) := by
  intro k
  simp only
  rw [T1_succ, ← deriv_p τ k, (hermite_p_conditions τ hτ0 hτ1 k).2.2.2.1]
  simp only [quint, D, cA]
  norm_num
  rw [mu_succ, one_div]

lemma matchA2 : Match (T1 τ) (fun k => D (D (cA τ k))) := by
  intro k
  simp only
  rw [T1_succ, ← deriv2_p τ k, (hermite_p_conditions τ hτ0 hτ1 k).2.2.2.2.2]
  simp only [quint, D, cA]
  norm_num

end

lemma matchB0 : Match T2 cB := by
  intro k
  have : T2 (k + 1) - T2 k = 1 := by unfold T2; push_cast; ring
  rw [this, quint_cB k, (q_interpolation k).2.1]
  simp only [quint, cB, f22knot]
  push_cast; ring

lemma matchB1 : Match T2 (fun k => D (cB k)) := by
  intro k
  have : T2 (k + 1) - T2 k = 1 := by unfold T2; push_cast; ring
  simp only
  rw [this, ← deriv_q k, (q_interpolation k).2.2.2.1]
  simp only [quint, D, cB]
  push_cast; ring_nf

lemma matchB2 : Match T2 (fun k => D (D (cB k))) := by
  intro k
  have : T2 (k + 1) - T2 k = 1 := by unfold T2; push_cast; ring
  simp only
  rw [this, ← deriv2_q k, (q_interpolation k).2.2.2.2.2]
  simp only [quint, D, cB]
  push_cast; ring_nf

end SNOneD



open Filter Topology Set SNGlue SlowConvergence.Newton SNOneD

namespace SNAB

noncomputable def A (τ : ℝ) : ℝ → ℝ := S0 (T1 τ) (cA τ)
noncomputable def A1 (τ : ℝ) : ℝ → ℝ := S1 (T1 τ) (cA τ)
noncomputable def A2 (τ : ℝ) : ℝ → ℝ := S2 (T1 τ) (cA τ)
noncomputable def B : ℝ → ℝ := S0 T2 cB
noncomputable def B1 : ℝ → ℝ := S1 T2 cB
noncomputable def B2 : ℝ → ℝ := S2 T2 cB

section
variable {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
include hτ0 hτ1

lemma A_hasDerivAt (t : ℝ) : HasDerivAt (A τ) (A1 τ t) t :=
  S0_hasDerivAt (T1_mono τ) (T1_zero τ) (T1_unbounded hτ0 hτ1) (matchA0 hτ0 hτ1)
    (matchA1 hτ0 hτ1) (matchA2 hτ0 hτ1) t

lemma A1_hasDerivAt (t : ℝ) : HasDerivAt (A1 τ) (A2 τ t) t :=
  S1_hasDerivAt (T1_mono τ) (T1_zero τ) (T1_unbounded hτ0 hτ1) (matchA0 hτ0 hτ1)
    (matchA1 hτ0 hτ1) (matchA2 hτ0 hτ1) t

lemma A_contDiff : ContDiff ℝ 2 (A τ) :=
  S0_contDiff (T1_mono τ) (T1_zero τ) (T1_unbounded hτ0 hτ1) (matchA0 hτ0 hτ1)
    (matchA1 hτ0 hτ1) (matchA2 hτ0 hτ1)

lemma A_on (k : ℕ) {t : ℝ} (h1 : T1 τ k ≤ t) (h2 : t ≤ T1 τ (k + 1)) :
    A τ t = quint (cA τ k) (t - T1 τ k) :=
  glue_eq_on (T1_mono τ) (T1_zero τ) (match_piece (matchA0 hτ0 hτ1)) k h1 h2

lemma A1_on (k : ℕ) {t : ℝ} (h1 : T1 τ k ≤ t) (h2 : t ≤ T1 τ (k + 1)) :
    A1 τ t = quint (D (cA τ k)) (t - T1 τ k) :=
  glue_eq_on (T1_mono τ) (T1_zero τ) (match_piece (matchA1 hτ0 hτ1)) k h1 h2

lemma A2_on (k : ℕ) {t : ℝ} (h1 : T1 τ k ≤ t) (h2 : t ≤ T1 τ (k + 1)) :
    A2 τ t = quint (D (D (cA τ k))) (t - T1 τ k) :=
  glue_eq_on (T1_mono τ) (T1_zero τ) (match_piece (matchA2 hτ0 hτ1)) k h1 h2

lemma A_neg {t : ℝ} (ht : t ≤ 0) : A τ t = quint (trunc2 (cA τ 0)) t :=
  glue_eq_neg (T1_mono τ) (T1_zero τ) (by simp [piece, T1_zero, quint, trunc2]) ht

lemma A2_neg {t : ℝ} (ht : t ≤ 0) : A2 τ t = quint (D (D (trunc2 (cA τ 0)))) t :=
  glue_eq_neg (T1_mono τ) (T1_zero τ) (by simp [piece, T1_zero, quint, trunc2, D]) ht

lemma phi_abs_le (k : ℕ) : |phi τ k| ≤ 1 := by
  unfold phi
  have h := SlowConvergence.Newton.psi_mem τ hτ0 hτ1 k
  rw [abs_neg]; exact h.2.le

lemma A2_bound (t : ℝ) : |A2 τ t| ≤ 151 := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [A2_neg hτ0 hτ1 ht.le]; simp [quint, D, trunc2, cA]; norm_num
  · obtain ⟨k, hk1, hk2⟩ := exists_piece (T1_zero τ) (T1_unbounded hτ0 hτ1) ht
    rw [A2_on hτ0 hτ1 k hk1 hk2.le, ← deriv2_p]
    have hu : t - T1 τ k ∈ Icc (0 : ℝ) (mu τ k) := by
      constructor
      · linarith
      · have := T1_succ τ k; linarith
    have := p_second_deriv_bound τ hτ0 hτ1 k
    exact (this.1 _ hu).trans this.2

lemma A_lower (t : ℝ) : -1 / 2 ≤ A τ t := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [A_neg hτ0 hτ1 ht.le]
    simp only [quint, trunc2, cA]
    norm_num
    have h1 := (bounded_below τ hτ0 hτ1 1).1
    have h2 : 0 ≤ (1 : ℝ) := by norm_num
    have hm := mu_le_one hτ0 hτ1 0
    have hm0 := mu_pos τ 0
    have hc : (0 : ℝ) ≤ 1 / 2 * (1 / ((0 : ℕ) + 1 : ℝ)) ^ (1 + 2 * eta τ) := by positivity
    norm_num at hc
    nlinarith [sq_nonneg (t - mu τ 0)]
  · obtain ⟨k, hk1, hk2⟩ := exists_piece (T1_zero τ) (T1_unbounded hτ0 hτ1) ht
    rw [A_on hτ0 hτ1 k hk1 hk2.le, quint_cA]
    have hu : t - T1 τ k ∈ Icc (0 : ℝ) (mu τ k) := by
      constructor
      · linarith
      · have := T1_succ τ k; linarith
    have := bounded_below τ hτ0 hτ1 (k + 1)
    have := (bounded_below τ hτ0 hτ1 k).2.2.2.2.1 _ hu
    linarith

lemma A2_closed (k : ℕ) (θ : ℝ) :
    quint (D (D (cA τ k))) (θ * mu τ k) = 1 + phi τ k * (-24 * θ + 84 * θ ^ 2 - 60 * θ ^ 3) := by
  have hm := (mu_pos τ k).ne'
  simp only [quint, D, cA]
  norm_num
  field_simp
  ring

lemma A2_lip (k : ℕ) {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |quint (D (D (cA τ k))) (θ * mu τ k) - quint (D (D (cA τ k))) (θ' * mu τ k)|
      ≤ 400 * |θ - θ'| := by
  rw [A2_closed hτ0 hτ1, A2_closed hτ0 hτ1]
  have e : 1 + phi τ k * (-24 * θ + 84 * θ ^ 2 - 60 * θ ^ 3)
      - (1 + phi τ k * (-24 * θ' + 84 * θ' ^ 2 - 60 * θ' ^ 3))
      = phi τ k * ((θ - θ') * (-24 + 84 * (θ + θ') - 60 * (θ ^ 2 + θ * θ' + θ' ^ 2))) := by ring
  rw [e, abs_mul, abs_mul]
  have hR : |-24 + 84 * (θ + θ') - 60 * (θ ^ 2 + θ * θ' + θ' ^ 2)| ≤ 400 := by
    have a1 : θ ^ 2 ≤ 1 := by nlinarith
    have a2 : θ' ^ 2 ≤ 1 := by nlinarith
    have a3 : θ * θ' ≤ 1 := by nlinarith
    have b1 : 0 ≤ θ ^ 2 := sq_nonneg _
    have b2 : 0 ≤ θ' ^ 2 := sq_nonneg _
    have b3 : 0 ≤ θ * θ' := mul_nonneg h0 h0'
    rw [abs_le]; constructor <;> linarith
  have hp := phi_abs_le hτ0 hτ1 k
  have := abs_nonneg (θ - θ')
  calc |phi τ k| * (|θ - θ'| * |-24 + 84 * (θ + θ') - 60 * (θ ^ 2 + θ * θ' + θ' ^ 2)|)
      ≤ 1 * (|θ - θ'| * 400) := by
        apply mul_le_mul hp (mul_le_mul_of_nonneg_left hR this) (by positivity) (by norm_num)
    _ = 400 * |θ - θ'| := by ring

end

lemma B_hasDerivAt (t : ℝ) : HasDerivAt B (B1 t) t :=
  S0_hasDerivAt T2_mono T2_zero T2_unbounded matchB0 matchB1 matchB2 t

lemma B1_hasDerivAt (t : ℝ) : HasDerivAt B1 (B2 t) t :=
  S1_hasDerivAt T2_mono T2_zero T2_unbounded matchB0 matchB1 matchB2 t

lemma B_contDiff : ContDiff ℝ 2 B :=
  S0_contDiff T2_mono T2_zero T2_unbounded matchB0 matchB1 matchB2

lemma B_on (k : ℕ) {t : ℝ} (h1 : T2 k ≤ t) (h2 : t ≤ T2 (k + 1)) :
    B t = quint (cB k) (t - T2 k) :=
  glue_eq_on T2_mono T2_zero (match_piece matchB0) k h1 h2

lemma B1_on (k : ℕ) {t : ℝ} (h1 : T2 k ≤ t) (h2 : t ≤ T2 (k + 1)) :
    B1 t = quint (D (cB k)) (t - T2 k) :=
  glue_eq_on T2_mono T2_zero (match_piece matchB1) k h1 h2

lemma B2_on (k : ℕ) {t : ℝ} (h1 : T2 k ≤ t) (h2 : t ≤ T2 (k + 1)) :
    B2 t = quint (D (D (cB k))) (t - T2 k) :=
  glue_eq_on T2_mono T2_zero (match_piece matchB2) k h1 h2

lemma B_neg {t : ℝ} (ht : t ≤ 0) : B t = quint (trunc2 (cB 0)) t :=
  glue_eq_neg T2_mono T2_zero (by simp [piece, T2_zero, quint, trunc2]) ht

lemma B2_neg {t : ℝ} (ht : t ≤ 0) : B2 t = quint (D (D (trunc2 (cB 0)))) t :=
  glue_eq_neg T2_mono T2_zero (by simp [piece, T2_zero, quint, trunc2, D]) ht

lemma B2_bound (t : ℝ) : |B2 t| ≤ 219 := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [B2_neg ht.le]; simp [quint, D, trunc2, cB]; norm_num
  · obtain ⟨k, hk1, hk2⟩ := exists_piece T2_zero T2_unbounded ht
    rw [B2_on k hk1 hk2.le, ← deriv2_q]
    have hu : t - T2 k ∈ Icc (0 : ℝ) 1 := by
      unfold T2 at *; push_cast at *; constructor <;> linarith
    exact q_second_deriv_bound k _ hu

lemma B_lower {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (t : ℝ) : -1 / 2 ≤ B t := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [B_neg ht.le]
    simp only [quint, trunc2, cB]
    norm_num
    have h1 := (bounded_below τ hτ0 hτ1 1).2.1
    nlinarith [sq_nonneg (t - 1)]
  · obtain ⟨k, hk1, hk2⟩ := exists_piece T2_zero T2_unbounded ht
    rw [B_on k hk1 hk2.le, quint_cB]
    have hu : t - T2 k ∈ Icc (0 : ℝ) 1 := by
      unfold T2 at *; push_cast at *; constructor <;> linarith
    have := bounded_below τ hτ0 hτ1 (k + 1)
    have := (bounded_below τ hτ0 hτ1 k).2.2.2.2.2 _ hu
    linarith

lemma B2_lip (k : ℕ) {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |quint (D (D (cB k))) θ - quint (D (D (cB k))) θ'| ≤ 500 * |θ - θ'| := by
  set b := (1 / ((k : ℝ) + 1)) ^ 2 with hb
  set c := (1 / ((k : ℝ) + 2)) ^ 2 with hc
  have hb0 : 0 ≤ b := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb]; apply pow_le_one₀ (by positivity)
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hc1 : c ≤ 1 := by
    rw [hc]; apply pow_le_one₀ (by positivity)
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have e : quint (D (D (cB k))) θ - quint (D (D (cB k))) θ'
      = (θ - θ') * (3 * (9 * c - b) + 6 * (-16 * c + 2 * b) * (θ + θ')
          + 10 * (7 * c - b) * (θ ^ 2 + θ * θ' + θ' ^ 2)) := by
    rw [hb, hc]
    simp only [quint, D, cB]
    norm_num
    ring
  rw [e, abs_mul]
  set s := θ + θ'
  set w := θ ^ 2 + θ * θ' + θ' ^ 2
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 2 := by linarith
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 3 := by nlinarith
  have hR : |3 * (9 * c - b) + 6 * (-16 * c + 2 * b) * s + 10 * (7 * c - b) * w| ≤ 500 := by
    have m1 : c * s ≤ 2 := by nlinarith
    have m2 : b * s ≤ 2 := by nlinarith
    have m3 : c * w ≤ 3 := by nlinarith
    have m4 : b * w ≤ 3 := by nlinarith
    have n1 : 0 ≤ c * s := mul_nonneg hc0 hs0
    have n2 : 0 ≤ b * s := mul_nonneg hb0 hs0
    have n3 : 0 ≤ c * w := mul_nonneg hc0 hw0
    have n4 : 0 ≤ b * w := mul_nonneg hb0 hw0
    rw [abs_le]; constructor <;> nlinarith
  have := abs_nonneg (θ - θ')
  calc |θ - θ'| * |3 * (9 * c - b) + 6 * (-16 * c + 2 * b) * s + 10 * (7 * c - b) * w|
      ≤ |θ - θ'| * 500 := mul_le_mul_of_nonneg_left hR this
    _ = 500 * |θ - θ'| := by ring

end SNAB



open Filter Topology Set SNGlue SlowConvergence.Newton SNOneD SNAB
open scoped RealInnerProductSpace

namespace SN2D

noncomputable def e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
noncomputable def e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
noncomputable def P0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight e0
noncomputable def P1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj (1 : Fin 2)).smulRight e1

noncomputable def F (τ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ := A τ (y 0) + B (y 1)
noncomputable def G (τ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  A1 τ (y 0) • e0 + B1 (y 1) • e1
noncomputable def H (τ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  A2 τ (y 0) • P0 + B2 (y 1) • P1

lemma inner2 (u v : EuclideanSpace ℝ (Fin 2)) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma G0 (τ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : G τ y 0 = A1 τ (y 0) := by
  simp [G, e0, e1, EuclideanSpace.single_apply]
lemma G1 (τ : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : G τ y 1 = B1 (y 1) := by
  simp [G, e0, e1, EuclideanSpace.single_apply]

lemma P0_apply (v : EuclideanSpace ℝ (Fin 2)) : P0 v = v 0 • e0 := by simp [P0]
lemma P1_apply (v : EuclideanSpace ℝ (Fin 2)) : P1 v = v 1 • e1 := by simp [P1]

lemma H0 (τ : ℝ) (y v : EuclideanSpace ℝ (Fin 2)) : H τ y v 0 = A2 τ (y 0) * v 0 := by
  simp [H, P0_apply, P1_apply, e0, e1, EuclideanSpace.single_apply]
lemma H1 (τ : ℝ) (y v : EuclideanSpace ℝ (Fin 2)) : H τ y v 1 = B2 (y 1) * v 1 := by
  simp [H, P0_apply, P1_apply, e0, e1, EuclideanSpace.single_apply]

lemma P0_norm : ‖P0‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [P0_apply, norm_smul, e0, EuclideanSpace.norm_single, norm_one, mul_one, one_mul]
  exact PiLp.norm_apply_le v 0

lemma P1_norm : ‖P1‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [P1_apply, norm_smul, e1, EuclideanSpace.norm_single, norm_one, mul_one, one_mul]
  exact PiLp.norm_apply_le v 1

lemma norm_comb (a b : ℝ) : ‖a • P0 + b • P1‖ ≤ |a| + |b| := by
  calc ‖a • P0 + b • P1‖ ≤ ‖a • P0‖ + ‖b • P1‖ := norm_add_le _ _
    _ = |a| * ‖P0‖ + |b| * ‖P1‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |a| * 1 + |b| * 1 := by
        gcongr
        · exact P0_norm
        · exact P1_norm
    _ = |a| + |b| := by ring

lemma Hk_apply' (k : ℕ) (v : EuclideanSpace ℝ (Fin 2)) :
    Hk k v = !₂[v 0, bk k * v 1] := by
  ext i
  fin_cases i <;> simp [Hk, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

section
variable {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
include hτ0 hτ1

lemma F_hasGradientAt (y : EuclideanSpace ℝ (Fin 2)) : HasGradientAt (F τ) (G τ y) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hA := (A_hasDerivAt hτ0 hτ1 (y 0)).comp_hasFDerivAt y
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt
  have hB := (B_hasDerivAt (y 1)).comp_hasFDerivAt y
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt
  have h := hA.add hB
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  rw [inner2, G0, G1]
  simp

lemma gradient_F : gradient (F τ) = G τ :=
  funext fun y => (F_hasGradientAt hτ0 hτ1 y).gradient

lemma G_hasFDerivAt (y : EuclideanSpace ℝ (Fin 2)) : HasFDerivAt (G τ) (H τ y) y := by
  have hA := ((A1_hasDerivAt hτ0 hτ1 (y 0)).comp_hasFDerivAt y
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt).smul_const e0
  have hB := ((B1_hasDerivAt (y 1)).comp_hasFDerivAt y
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt).smul_const e1
  have h := hA.add hB
  refine h.congr_fderiv ?_
  ext v i
  simp [H, P0, P1, smul_smul]

lemma hess_F : fderiv ℝ (gradient (F τ)) = H τ := by
  rw [gradient_F hτ0 hτ1]
  exact funext fun y => (G_hasFDerivAt hτ0 hτ1 y).fderiv

lemma xk_apply (k : ℕ) : xk τ k 0 = T1 τ k ∧ xk τ k 1 = (k : ℝ) := by
  induction k with
  | zero => simp [xk, T1]
  | succ k ih =>
    simp only [xk, PiLp.add_apply]
    rw [ih.1, ih.2]
    simp [T1, Finset.sum_range_succ]

lemma G_xk (k : ℕ) : G τ (xk τ k) = gk τ k := by
  obtain ⟨h0, h1⟩ := xk_apply hτ0 hτ1 (τ := τ) k
  have a : A1 τ (T1 τ k) = -mu τ k := by
    rw [A1_on hτ0 hτ1 k le_rfl (T1_mono τ (Nat.lt_succ_self k)).le]
    simp [quint, D, cA]
  have b : B1 (k : ℝ) = -bk k := by
    rw [show (k : ℝ) = T2 k from rfl, B1_on k le_rfl (T2_mono (Nat.lt_succ_self k)).le]
    simp [quint, D, cB, bk]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta]; rw [G0, h0, a]; simp [gk]
  · simp only [Fin.mk_one]; rw [G1, h1, b]; simp [gk]

lemma H_xk (k : ℕ) : H τ (xk τ k) = Hk k := by
  obtain ⟨h0, h1⟩ := xk_apply hτ0 hτ1 (τ := τ) k
  have a : A2 τ (T1 τ k) = 1 := by
    rw [A2_on hτ0 hτ1 k le_rfl (T1_mono τ (Nat.lt_succ_self k)).le]
    simp [quint, D, cA]; norm_num
  have b : B2 (k : ℝ) = bk k := by
    rw [show (k : ℝ) = T2 k from rfl, B2_on k le_rfl (T2_mono (Nat.lt_succ_self k)).le]
    simp [quint, D, cB, bk]; ring
  ext v i
  rw [Hk_apply']
  fin_cases i
  · simp only [Fin.zero_eta]; rw [H0, h0, a]; simp
  · simp only [Fin.mk_one]; rw [H1, h1, b]; simp

lemma F_xk (k : ℕ) : F τ (xk τ k) = fk τ k := by
  obtain ⟨h0, h1⟩ := xk_apply hτ0 hτ1 (τ := τ) k
  have a : A τ (T1 τ k) = f21knot τ k := by
    rw [A_on hτ0 hτ1 k le_rfl (T1_mono τ (Nat.lt_succ_self k)).le]
    simp only [sub_self, quint, cA, f21knot]; ring
  have b : B (k : ℝ) = f22knot k := by
    rw [show (k : ℝ) = T2 k from rfl, B_on k le_rfl (T2_mono (Nat.lt_succ_self k)).le]
    simp only [sub_self, quint, cB, f22knot]; ring
  unfold F; rw [h0, h1, a, b, (bounded_below τ hτ0 hτ1 k).2.2.1]

lemma H_lip (k : ℕ) (y z : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ segment ℝ (xk τ k) (xk τ (k + 1)))
    (hz : z ∈ segment ℝ (xk τ k) (xk τ (k + 1))) : ‖H τ y - H τ z‖ ≤ 900 * ‖y - z‖ := by
  have hs := (newton_step_conditions τ hτ0 hτ1 k).1
  obtain ⟨h0, h1⟩ := xk_apply hτ0 hτ1 (τ := τ) k
  rw [segment_eq_image'] at hy hz
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hy
  obtain ⟨θ', ⟨hθ0', hθ1'⟩, rfl⟩ := hz
  have hd : xk τ (k + 1) - xk τ k = !₂[mu τ k, 1] := hs
  rw [hd]
  have hm := mu_pos τ k
  have hT := T1_succ τ k
  have y0 : ∀ θ : ℝ, (xk τ k + θ • !₂[mu τ k, 1]) 0 = T1 τ k + θ * mu τ k := by
    intro θ; simp [h0]
  have y1 : ∀ θ : ℝ, (xk τ k + θ • !₂[mu τ k, 1]) 1 = T2 k + θ := by
    intro θ; simp [h1, T2]
  have a2 : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      A2 τ ((xk τ k + θ • !₂[mu τ k, 1]) 0) = quint (D (D (cA τ k))) (θ * mu τ k) := by
    intro θ h0 h1
    rw [y0, A2_on hτ0 hτ1 k (by nlinarith) (by nlinarith)]
    ring_nf
  have b2 : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      B2 ((xk τ k + θ • !₂[mu τ k, 1]) 1) = quint (D (D (cB k))) θ := by
    intro θ h0 h1
    have : T2 (k + 1) = T2 k + 1 := by simp [T2]
    rw [y1, B2_on k (by linarith) (by linarith)]
    ring_nf
  have e : H τ (xk τ k + θ • !₂[mu τ k, 1]) - H τ (xk τ k + θ' • !₂[mu τ k, 1])
      = (A2 τ ((xk τ k + θ • !₂[mu τ k, 1]) 0) - A2 τ ((xk τ k + θ' • !₂[mu τ k, 1]) 0)) • P0
        + (B2 ((xk τ k + θ • !₂[mu τ k, 1]) 1) - B2 ((xk τ k + θ' • !₂[mu τ k, 1]) 1)) • P1 := by
    simp only [H]; module
  rw [e]
  refine (norm_comb _ _).trans ?_
  rw [a2 θ hθ0 hθ1, a2 θ' hθ0' hθ1', b2 θ hθ0 hθ1, b2 θ' hθ0' hθ1']
  have l1 := A2_lip hτ0 hτ1 k hθ0 hθ1 hθ0' hθ1'
  have l2 := B2_lip k hθ0 hθ1 hθ0' hθ1'
  have hn : |θ - θ'| ≤ ‖xk τ k + θ • !₂[mu τ k, 1] - (xk τ k + θ' • !₂[mu τ k, 1])‖ := by
    have := PiLp.norm_apply_le (xk τ k + θ • !₂[mu τ k, 1] - (xk τ k + θ' • !₂[mu τ k, 1])) 1
    rw [PiLp.sub_apply, y1, y1, Real.norm_eq_abs] at this
    have e2 : T2 k + θ - (T2 k + θ') = θ - θ' := by ring
    rwa [e2] at this
  linarith

end

end SN2D

open SN2D in
theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
      (∃ M : ℝ, ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ M) ∧
      ∃ x : ℕ → EuclideanSpace ℝ (Fin 2), x 0 = 0 ∧
        (∀ k, (∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → 0 < ⟪fderiv ℝ (gradient f) (x k) v, v⟫) ∧
          fderiv ℝ (gradient f) (x k) (x (k + 1) - x k) = -gradient f (x k)) ∧
        (∃ L : ℝ, ∀ k, ∀ y ∈ segment ℝ (x k) (x (k + 1)), ∀ z ∈ segment ℝ (x k) (x (k + 1)),
          ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖) ∧
        (∀ k, f (x (k + 1)) = f (x k) + ⟪gradient f (x k), x (k + 1) - x k⟫
          + 1 / 2 * ⟪fderiv ℝ (gradient f) (x k) (x (k + 1) - x k), x (k + 1) - x k⟫) ∧
        (∀ k : ℕ, (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ)) ≤ ‖gradient f (x k)‖) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, ‖gradient f (x k)‖ ≤ ε →
          (⌊ε ^ (-(2 - τ))⌋₊ : ℝ) ≤ k + 1) := by
  have hg := gradient_F hτ0 hτ1
  have hH := hess_F hτ0 hτ1
  have glb : ∀ k : ℕ, (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ)) ≤ ‖gradient (F τ) (xk τ k)‖ := by
    intro k
    rw [hg, G_xk hτ0 hτ1]
    exact (gradient_lower_bound τ hτ0 hτ1).2 k
  refine ⟨F τ, ?_, ?_, ?_, xk τ, ?_, ?_, ?_, ?_, glb, ?_⟩
  · unfold F
    exact ((A_contDiff hτ0 hτ1).comp (EuclideanSpace.proj (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff).add
      (B_contDiff.comp (EuclideanSpace.proj (1 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff)
  · refine ⟨-1, ?_⟩
    rintro _ ⟨y, rfl⟩
    unfold F
    linarith [A_lower hτ0 hτ1 (y 0), B_lower hτ0 hτ1 (y 1)]
  · refine ⟨151 + 219, fun y => ?_⟩
    rw [hH]
    refine (norm_comb _ _).trans ?_
    linarith [A2_bound hτ0 hτ1 (y 0), B2_bound (y 1)]
  · ext i; fin_cases i <;> simp [xk]
  · intro k
    have hn := newton_step_conditions τ hτ0 hτ1 k
    rw [hH, hg, H_xk hτ0 hτ1, G_xk hτ0 hτ1]
    refine ⟨hn.2.2.2.2.1, ?_⟩
    have : xk τ (k + 1) - xk τ k = sk τ k := rfl
    rw [this]; exact hn.2.2.2.2.2.1
  · refine ⟨900, fun k y hy z hz => ?_⟩
    rw [hH]
    exact H_lip hτ0 hτ1 k y z hy hz
  · intro k
    have hn := newton_step_conditions τ hτ0 hτ1 k
    rw [hH, hg, H_xk hτ0 hτ1, G_xk hτ0 hτ1, F_xk hτ0 hτ1, F_xk hτ0 hτ1, ← hn.2.2.2.2.2.2]
    have : xk τ k + sk τ k = xk τ (k + 1) := by unfold sk; abel
    rw [this]
    rfl
  · intro ε hε0 hε1 k hk
    have h := (glb k).trans hk
    have ha : 0 < 2 - τ := by linarith
    have hb : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h2 : 1 / ((k : ℝ) + 1) ≤ ε ^ (2 - τ) := by
      have := Real.rpow_le_rpow (by positivity) h ha.le
      rwa [← Real.rpow_mul hb.le, one_div_mul_cancel ha.ne', Real.rpow_one] at this
    have h3 : ε ^ (-(2 - τ)) ≤ (k : ℝ) + 1 := by
      rw [Real.rpow_neg hε0.le]
      have := inv_anti₀ hb h2
      rwa [one_div, inv_inv] at this
    exact (Nat.floor_le (by positivity)).trans h3
