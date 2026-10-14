-- Prove2me | solution 1 for TPG.rc_bias_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T05:00:25.707951+00:00
-- url     : https://prove2.me/submissions/d42cf40f-d32a-48c9-9996-9961a76f3d5f

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge
import Theorems.Thm_TPG_mixing_contraction
import Theorems.Thm_TPG_integral_rcEst
import Theorems.Thm_TPG_gate_eq_meanReward

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace RCBias

variable {S : Type} [Fintype S]

/-! ### The `ℓ¹` norm of row vectors -/

/-- `ℓ¹` norm of a real vector indexed by a finite type. -/
noncomputable def l1 (v : S → ℝ) : ℝ := ∑ x, |v x|

theorem l1_nonneg (v : S → ℝ) : 0 ≤ l1 v := Finset.sum_nonneg fun x _ => abs_nonneg (v x)

theorem l1_add_le (v w : S → ℝ) : l1 (v + w) ≤ l1 v + l1 w := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => abs_add_le (v x) (w x)

theorem l1_smul (c : ℝ) (v : S → ℝ) : l1 (c • v) = |c| * l1 v := by
  unfold l1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [Pi.smul_apply, smul_eq_mul, abs_mul]

theorem l1_of_nonneg (v : S → ℝ) (hv : ∀ x, 0 ≤ v x) : l1 v = ∑ x, v x :=
  Finset.sum_congr rfl fun x _ => abs_of_nonneg (hv x)

/-- Hölder: `|v · r| ≤ ‖v‖₁ ‖r‖_∞`. -/
theorem abs_dotProduct_le (v r : S → ℝ) (C : ℝ) (hr : ∀ x, |r x| ≤ C) :
    |v ⬝ᵥ r| ≤ l1 v * C := by
  unfold l1
  simp only [dotProduct]
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hr x) (abs_nonneg _)

/-- If every row of `A` has `ℓ¹` norm at most `c`, then `‖v A‖₁ ≤ c ‖v‖₁`. -/
theorem l1_vecMul_le (v : S → ℝ) (A : Matrix S S ℝ) (c : ℝ) (hA : ∀ y, l1 (A y) ≤ c) :
    l1 (Matrix.vecMul v A) ≤ c * l1 v := by
  have h1 : ∀ x, |Matrix.vecMul v A x| ≤ ∑ y, |v y| * |A y x| := by
    intro x
    simp only [Matrix.vecMul, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun y _ => abs_mul _ _
  calc l1 (Matrix.vecMul v A) ≤ ∑ x, ∑ y, |v y| * |A y x| := Finset.sum_le_sum fun x _ => h1 x
    _ = ∑ y, |v y| * l1 (A y) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => by rw [l1, Finset.mul_sum]
    _ ≤ ∑ y, |v y| * c :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hA y) (abs_nonneg _)
    _ = c * l1 v := by rw [← Finset.sum_mul, mul_comm]; rfl

/-- If every row of `A` sums to `c`, then the entries of `v A` sum to `c` times those of `v`. -/
theorem sum_vecMul_eq (v : S → ℝ) (A : Matrix S S ℝ) (c : ℝ) (hA : ∀ y, ∑ x, A y x = c) :
    ∑ x, Matrix.vecMul v A x = c * ∑ x, v x := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, hA y, mul_comm]

/-! ### One-step kernels -/

theorem PMix_nonneg (E : Env S) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (t : ℕ) (y x : S) :
    0 ≤ E.PMix θ t y x := by
  unfold Env.PMix
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg hθ.1 (E.P_nonneg _ _ _ _))
    (mul_nonneg (by linarith [hθ.2]) (E.P_nonneg _ _ _ _))

theorem PMix_row_sum (E : Env S) (θ : ℝ) (t : ℕ) (y : S) : ∑ x, E.PMix θ t y x = 1 := by
  unfold Env.PMix
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, E.P_row_sum, E.P_row_sum]
  ring

theorem l1_PMix_row (E : Env S) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (t : ℕ) (y : S) :
    l1 (E.PMix θ t y) ≤ 1 := by
  rw [l1_of_nonneg _ (PMix_nonneg E θ hθ t y), PMix_row_sum]

/-- The kernel difference `Δ^u = P_1^u - P_0^u`. -/
def Dk (E : Env S) (u : ℕ) : Matrix S S ℝ := E.P u true - E.P u false

/-- `P_c^u = P_θ^u + (c - θ) Δ^u`. -/
theorem PMix_eq_add (E : Env S) (c θ : ℝ) (u : ℕ) :
    E.PMix c u = E.PMix θ u + (c - θ) • Dk E u := by
  unfold Env.PMix Dk
  ext y x
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem PMix_one_sub_zero (E : Env S) (u : ℕ) : E.PMix 1 u - E.PMix 0 u = Dk E u := by
  unfold Env.PMix Dk
  ext y x
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem Dk_row_sum (E : Env S) (u : ℕ) (y : S) : ∑ x, Dk E u y x = 0 := by
  unfold Dk
  simp only [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib, E.P_row_sum, E.P_row_sum, sub_self]

theorem tv_le_delta (E : Env S) (T u : ℕ) (hu : u < T) (y : S) :
    tvDist (E.P u true y) (E.P u false y) ≤ E.delta T := by
  unfold Env.delta
  have h1 : tvDist (E.P u true y) (E.P u false y)
      ≤ ⨆ x : S, tvDist (E.P u true x) (E.P u false x) :=
    le_ciSup (f := fun x : S => tvDist (E.P u true x) (E.P u false x))
      (Set.finite_range _).bddAbove y
  have h2 := le_ciSup
    (f := fun t : Fin T => ⨆ x : S, tvDist (E.P (t : ℕ) true x) (E.P (t : ℕ) false x))
    (Set.finite_range _).bddAbove ⟨u, hu⟩
  exact h1.trans h2

theorem delta_nonneg (E : Env S) (T : ℕ) : 0 ≤ E.delta T := by
  unfold Env.delta
  refine Real.iSup_nonneg fun t => Real.iSup_nonneg fun x => ?_
  unfold tvDist
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem l1_Dk_row (E : Env S) (T u : ℕ) (hu : u < T) (y : S) :
    l1 (Dk E u y) ≤ 2 * E.delta T := by
  have h := tv_le_delta E T u hu y
  unfold tvDist at h
  have h2 : l1 (Dk E u y) = ∑ x, |E.P u true y x - E.P u false y x| := rfl
  linarith

theorem l1_vecMul_PMix_le (E : Env S) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (t : ℕ) (v : S → ℝ) :
    l1 (Matrix.vecMul v (E.PMix θ t)) ≤ l1 v := by
  simpa using l1_vecMul_le v (E.PMix θ t) 1 (l1_PMix_row E θ hθ t)

theorem sum_vecMul_PMix (E : Env S) (θ : ℝ) (t : ℕ) (v : S → ℝ) :
    ∑ x, Matrix.vecMul v (E.PMix θ t) x = ∑ x, v x := by
  simpa using sum_vecMul_eq v (E.PMix θ t) 1 (PMix_row_sum E θ t)

/-- `‖v Δ^u‖₁ ≤ 2 δ ‖v‖₁` for `u < T`. -/
theorem l1_vecMul_Dk_le (E : Env S) (T u : ℕ) (hu : u < T) (v : S → ℝ) :
    l1 (Matrix.vecMul v (Dk E u)) ≤ 2 * E.delta T * l1 v :=
  l1_vecMul_le v (Dk E u) _ (l1_Dk_row E T u hu)

/-- `v Δ^u` is a zero-sum vector. -/
theorem sum_vecMul_Dk (E : Env S) (u : ℕ) (v : S → ℝ) :
    ∑ x, Matrix.vecMul v (Dk E u) x = 0 := by
  simpa using sum_vecMul_eq v (Dk E u) 0 (Dk_row_sum E u)

/-! ### Rewards -/

theorem abs_r_le (E : Env S) (M : ℝ) (hM : E.RewardBound M) (z : Bool) (x : S) :
    |E.r z x| ≤ M := by
  unfold Env.r
  have h1 : Set.Icc (-M) M ∈ ae (E.R x z) :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 (hM x z)
  have h2 : ∀ᵐ y ∂(E.R x z), ‖y‖ ≤ M := by
    filter_upwards [h1] with y hy
    exact abs_le.2 hy
  have h3 := norm_integral_le_of_norm_le_const h2
  simpa using h3

theorem rMix_eq (E : Env S) (θ : ℝ) : E.rMix θ = θ • E.r true + (1 - θ) • E.r false := by
  funext x
  simp [Env.rMix]

theorem rMix_one (E : Env S) : E.rMix 1 = E.r true := by
  funext x
  simp [Env.rMix]

theorem rMix_zero (E : Env S) : E.rMix 0 = E.r false := by
  funext x
  simp [Env.rMix]

/-! ### The functions `G_n(γ) = ∑_{j<n} γ^j` and `Ψ_n(γ)` -/

theorem Psi_eq (n : ℕ) (γ : ℝ) :
    Psi n γ = ∑ j ∈ Finset.range (n - 1), ((j : ℝ) + 1) * γ ^ j := by
  unfold Psi
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem Psi_zero (γ : ℝ) : Psi 0 γ = 0 := by simp [Psi]

theorem Psi_nonneg (n : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) : 0 ≤ Psi n γ := by
  unfold Psi
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

theorem Psi_aux (m : ℕ) (γ : ℝ) :
    ∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1) * γ ^ j
      = γ * ∑ j ∈ Finset.range m, ((j : ℝ) + 1) * γ ^ j + ∑ j ∈ Finset.range (m + 1), γ ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := Finset.sum_range_succ (fun j : ℕ => ((j : ℝ) + 1) * γ ^ j) (m + 1)
    have h2 := Finset.sum_range_succ (fun j : ℕ => ((j : ℝ) + 1) * γ ^ j) m
    have h3 := Finset.sum_range_succ (fun j : ℕ => γ ^ j) (m + 1)
    push_cast at h1 h2 h3 ⊢
    linear_combination h1 - γ * h2 - h3 + ih

/-- `Ψ_{n+1}(γ) = γ Ψ_n(γ) + G_n(γ)`. -/
theorem Psi_succ (n : ℕ) (γ : ℝ) :
    Psi (n + 1) γ = γ * Psi n γ + ∑ j ∈ Finset.range n, γ ^ j := by
  rw [Psi_eq, Psi_eq]
  cases n with
  | zero => simp
  | succ m => simpa using Psi_aux m γ

/-! ### Products of mixture kernels -/

section Products

variable [DecidableEq S]

/-- `P_{q_a}^a P_{q_{a+1}}^{a+1} ⋯ P_{q_{b-1}}^{b-1}` for a time-dependent allocation `q`. -/
noncomputable def kprod (E : Env S) (q : ℕ → ℝ) (a b : ℕ) : Matrix S S ℝ :=
  ((List.Ico a b).map (fun s => E.PMix (q s) s)).prod

theorem PProd_eq_kprod (E : Env S) (θ : ℝ) (a b : ℕ) :
    E.PProd θ a b = kprod E (fun _ => θ) a b := rfl

theorem kprod_of_le (E : Env S) (q : ℕ → ℝ) {a b : ℕ} (h : b ≤ a) : kprod E q a b = 1 := by
  unfold kprod
  rw [List.Ico.eq_nil_of_le h]
  simp

theorem kprod_succ (E : Env S) (q : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    kprod E q a (b + 1) = kprod E q a b * E.PMix (q b) b := by
  unfold kprod
  rw [List.Ico.succ_top h, List.map_append, List.prod_append]
  simp

theorem kprod_cons (E : Env S) (q : ℕ → ℝ) {a b : ℕ} (h : a < b) :
    kprod E q a b = E.PMix (q a) a * kprod E q (a + 1) b := by
  unfold kprod
  rw [List.Ico.eq_cons h, List.map_cons, List.prod_cons]

theorem kprod_mul (E : Env S) (q : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    kprod E q a b * kprod E q b c = kprod E q a c := by
  unfold kprod
  rw [← List.prod_append, ← List.map_append, List.Ico.append_consecutive hab hbc]

theorem kprod_congr (E : Env S) {q q' : ℕ → ℝ} {a b : ℕ}
    (h : ∀ s, a ≤ s → s < b → q s = q' s) : kprod E q a b = kprod E q' a b := by
  unfold kprod
  congr 1
  refine List.map_congr_left fun s hs => ?_
  rw [List.Ico.mem] at hs
  rw [h s hs.1 hs.2]

theorem l1_vecMul_kprod_le (E : Env S) (q : ℕ → ℝ) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) (a b : ℕ)
    (v : S → ℝ) : l1 (Matrix.vecMul v (kprod E q a b)) ≤ l1 v := by
  rcases le_total b a with h | h
  · rw [kprod_of_le E q h, Matrix.vecMul_one]
  · induction b, h using Nat.le_induction with
    | base => rw [kprod_of_le E q le_rfl, Matrix.vecMul_one]
    | succ n hn ih =>
      rw [kprod_succ E q hn, ← Matrix.vecMul_vecMul]
      exact (l1_vecMul_PMix_le E _ (hq n) n _).trans ih

theorem sum_vecMul_kprod (E : Env S) (q : ℕ → ℝ) (a b : ℕ) (v : S → ℝ) :
    ∑ x, Matrix.vecMul v (kprod E q a b) x = ∑ x, v x := by
  rcases le_total b a with h | h
  · rw [kprod_of_le E q h, Matrix.vecMul_one]
  · induction b, h using Nat.le_induction with
    | base => rw [kprod_of_le E q le_rfl, Matrix.vecMul_one]
    | succ n hn ih =>
      rw [kprod_succ E q hn, ← Matrix.vecMul_vecMul, sum_vecMul_PMix]
      exact ih

/-- Multi-step contraction of zero-sum row vectors (black box `TPG.mixing_contraction`). -/
theorem contraction (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (q : ℕ → ℝ) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ T)
    (v : S → ℝ) (hv : ∑ x, v x = 0) :
    l1 (Matrix.vecMul v (kprod E q a b)) ≤ γ ^ (b - a) * l1 v :=
  TPG.mixing_contraction E T γ hγ hmix q hq a b hab hb v hv

/-- One-step contraction of zero-sum row vectors under `P_θ^t`. -/
theorem contraction_step (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (t : ℕ) (ht : t < T) (v : S → ℝ) (hv : ∑ x, v x = 0) :
    l1 (Matrix.vecMul v (E.PMix θ t)) ≤ γ * l1 v := by
  have h := contraction E T γ hγ hmix (fun _ => θ) (fun _ => hθ) t (t + 1) (Nat.le_succ t) ht v hv
  rw [kprod_succ E _ le_rfl, kprod_of_le E _ le_rfl, one_mul, Nat.add_sub_cancel_left, pow_one] at h
  exact h

/-- Generic recursion: if `v_s = 0`, `v_{t+1} = v_t P_θ^t + e_t` with `e_t` zero-sum and
`‖e_t‖₁ ≤ C g(t - s)`, and `h(0) = 0`, `h(n+1) = γ h(n) + g(n)`, then `v_t` is zero-sum and
`‖v_t‖₁ ≤ C h(t - s)`. -/
theorem rec_bound (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (s : ℕ) (v e : ℕ → S → ℝ) (C : ℝ) (g h : ℕ → ℝ)
    (hv0 : v s = 0)
    (hrec : ∀ t, s ≤ t → t < T → v (t + 1) = Matrix.vecMul (v t) (E.PMix θ t) + e t)
    (he0 : ∀ t, s ≤ t → t < T → ∑ x, e t x = 0)
    (hebd : ∀ t, s ≤ t → t < T → l1 (e t) ≤ C * g (t - s))
    (hh0 : h 0 = 0) (hhrec : ∀ n, h (n + 1) = γ * h n + g n) :
    ∀ t, s ≤ t → t ≤ T → (∑ x, v t x = 0) ∧ l1 (v t) ≤ C * h (t - s) := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base =>
    intro _
    rw [hv0, Nat.sub_self, hh0]
    simp [l1]
  | succ n hn ih =>
    intro hnT
    have hnT' : n < T := by omega
    obtain ⟨ih0, ih1⟩ := ih (by omega)
    rw [hrec n hn hnT']
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, sum_vecMul_PMix, ih0, he0 n hn hnT', add_zero]
    · have hexp : n + 1 - s = (n - s) + 1 := by omega
      rw [hexp, hhrec]
      calc l1 (Matrix.vecMul (v n) (E.PMix θ n) + e n)
          ≤ l1 (Matrix.vecMul (v n) (E.PMix θ n)) + l1 (e n) := l1_add_le _ _
        _ ≤ γ * l1 (v n) + C * g (n - s) :=
            add_le_add (contraction_step E T γ hγ hmix θ hθ n hnT' _ ih0) (hebd n hn hnT')
        _ ≤ γ * (C * h (n - s)) + C * g (n - s) :=
            add_le_add (mul_le_mul_of_nonneg_left ih1 hγ) le_rfl
        _ = C * (γ * h (n - s) + g (n - s)) := by ring

/-! ### Constant-allocation products and state distributions -/

theorem PProd_self (E : Env S) (θ : ℝ) (a : ℕ) : E.PProd θ a a = 1 :=
  kprod_of_le E _ le_rfl

theorem PProd_succ (E : Env S) (θ : ℝ) {a b : ℕ} (h : a ≤ b) :
    E.PProd θ a (b + 1) = E.PProd θ a b * E.PMix θ b :=
  kprod_succ E _ h

theorem PProd_mul (E : Env S) (θ : ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    E.PProd θ a b * E.PProd θ b c = E.PProd θ a c :=
  kprod_mul E _ hab hbc

omit [DecidableEq S] in
theorem l1_rho (E : Env S) : l1 E.ρ = 1 := by
  rw [l1_of_nonneg _ E.ρ_nonneg, E.ρ_sum]

theorem stateDist_vecMul (E : Env S) (θ : ℝ) {s t : ℕ} (hst : s ≤ t) :
    Matrix.vecMul (E.stateDist θ s) (E.PProd θ s t) = E.stateDist θ t := by
  unfold Env.stateDist
  rw [Matrix.vecMul_vecMul, PProd_mul E θ (Nat.zero_le s) hst]

theorem l1_stateDist_le (E : Env S) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (t : ℕ) :
    l1 (E.stateDist θ t) ≤ 1 := by
  have h := l1_vecMul_kprod_le E (fun _ => θ) (fun _ => hθ) 0 t E.ρ
  rw [l1_rho] at h
  exact h

/-! ### The first-order term and the three recursive bounds -/

/-- First-order term `A(ν; s, t) = ∑_{u ∈ [s,t)} ν Π_θ(s,u) Δ^u Π_θ(u+1,t)`. -/
noncomputable def Avec (E : Env S) (θ : ℝ) (ν : S → ℝ) (s t : ℕ) : S → ℝ :=
  ∑ u ∈ Finset.Ico s t,
    Matrix.vecMul (Matrix.vecMul (Matrix.vecMul ν (E.PProd θ s u)) (Dk E u)) (E.PProd θ (u + 1) t)

theorem Avec_self (E : Env S) (θ : ℝ) (ν : S → ℝ) (s : ℕ) : Avec E θ ν s s = 0 := by
  simp [Avec]

theorem Avec_succ (E : Env S) (θ : ℝ) (ν : S → ℝ) {s t : ℕ} (hst : s ≤ t) :
    Avec E θ ν s (t + 1)
      = Matrix.vecMul (Avec E θ ν s t) (E.PMix θ t)
        + Matrix.vecMul (Matrix.vecMul ν (E.PProd θ s t)) (Dk E t) := by
  unfold Avec
  rw [Finset.sum_Ico_succ_top hst, PProd_self, Matrix.vecMul_one, Matrix.sum_vecMul]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_Ico] at hu
  rw [PProd_succ E θ (by omega : u + 1 ≤ t)]
  exact (Matrix.vecMul_vecMul _ _ _).symm

/-- `ν Π_c(s,t) - ν Π_θ(s,t)` is zero-sum with `ℓ¹` norm at most `2 δ |c-θ| ‖ν‖₁ G_{t-s}(γ)`. -/
theorem diff_bound (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (θ c : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (ν : S → ℝ) (s t : ℕ)
    (hst : s ≤ t) (htT : t ≤ T) :
    (∑ x, (Matrix.vecMul ν (E.PProd c s t) - Matrix.vecMul ν (E.PProd θ s t)) x = 0) ∧
      l1 (Matrix.vecMul ν (E.PProd c s t) - Matrix.vecMul ν (E.PProd θ s t))
        ≤ 2 * E.delta T * |c - θ| * l1 ν * ∑ j ∈ Finset.range (t - s), γ ^ j := by
  have hδ := delta_nonneg E T
  refine rec_bound E T γ hγ hmix θ hθ s
    (fun t => Matrix.vecMul ν (E.PProd c s t) - Matrix.vecMul ν (E.PProd θ s t))
    (fun t => (c - θ) • Matrix.vecMul (Matrix.vecMul ν (E.PProd c s t)) (Dk E t))
    (2 * E.delta T * |c - θ| * l1 ν)
    (fun _ => 1) (fun n => ∑ j ∈ Finset.range n, γ ^ j) ?_ ?_ ?_ ?_ ?_ ?_ t hst htT
  · simp [PProd_self]
  · intro t hst _
    rw [PProd_succ E c hst, PProd_succ E θ hst, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      PMix_eq_add E c θ t, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.sub_vecMul]
    abel
  · intro t _ _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, sum_vecMul_Dk, mul_zero]
  · intro t _ htT
    rw [l1_smul, mul_one]
    calc |c - θ| * l1 (Matrix.vecMul (Matrix.vecMul ν (E.PProd c s t)) (Dk E t))
        ≤ |c - θ| * (2 * E.delta T * l1 (Matrix.vecMul ν (E.PProd c s t))) :=
          mul_le_mul_of_nonneg_left (l1_vecMul_Dk_le E T t htT _) (abs_nonneg _)
      _ ≤ |c - θ| * (2 * E.delta T * l1 ν) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (l1_vecMul_kprod_le E (fun _ => c) (fun _ => hc) s t ν)
              (by linarith)) (abs_nonneg _)
      _ = 2 * E.delta T * |c - θ| * l1 ν := by ring
  · simp
  · intro n
    exact geom_sum_succ

/-- `A(ν; s, t)` is zero-sum with `ℓ¹` norm at most `2 δ ‖ν‖₁ G_{t-s}(γ)`. -/
theorem Avec_bound (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ν : S → ℝ) (s t : ℕ) (hst : s ≤ t) (htT : t ≤ T) :
    (∑ x, Avec E θ ν s t x = 0) ∧
      l1 (Avec E θ ν s t) ≤ 2 * E.delta T * l1 ν * ∑ j ∈ Finset.range (t - s), γ ^ j := by
  have hδ := delta_nonneg E T
  refine rec_bound E T γ hγ hmix θ hθ s (fun t => Avec E θ ν s t)
    (fun t => Matrix.vecMul (Matrix.vecMul ν (E.PProd θ s t)) (Dk E t))
    (2 * E.delta T * l1 ν)
    (fun _ => 1) (fun n => ∑ j ∈ Finset.range n, γ ^ j) ?_ ?_ ?_ ?_ ?_ ?_ t hst htT
  · exact Avec_self E θ ν s
  · intro t hst _
    exact Avec_succ E θ ν hst
  · intro t _ _
    exact sum_vecMul_Dk E t _
  · intro t _ htT
    simp only [mul_one]
    exact (l1_vecMul_Dk_le E T t htT _).trans
      (mul_le_mul_of_nonneg_left (l1_vecMul_kprod_le E (fun _ => θ) (fun _ => hθ) s t ν)
        (by linarith))
  · simp
  · intro n
    exact geom_sum_succ

/-- Second-order remainder:
`‖ν Π_c(s,t) - ν Π_θ(s,t) - (c-θ) A(ν; s, t)‖₁ ≤ 4 (c-θ)² δ² ‖ν‖₁ Ψ_{t-s}(γ)`. -/
theorem rem_bound (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (θ c : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (ν : S → ℝ) (s t : ℕ)
    (hst : s ≤ t) (htT : t ≤ T) :
    l1 (Matrix.vecMul ν (E.PProd c s t) - Matrix.vecMul ν (E.PProd θ s t)
          - (c - θ) • Avec E θ ν s t)
      ≤ 4 * (c - θ) ^ 2 * E.delta T ^ 2 * l1 ν * Psi (t - s) γ := by
  have hδ := delta_nonneg E T
  refine (rec_bound E T γ hγ hmix θ hθ s
    (fun t => Matrix.vecMul ν (E.PProd c s t) - Matrix.vecMul ν (E.PProd θ s t)
      - (c - θ) • Avec E θ ν s t)
    (fun t => (c - θ) • Matrix.vecMul
      (Matrix.vecMul ν (E.PProd c s t) - Matrix.vecMul ν (E.PProd θ s t)) (Dk E t))
    (4 * (c - θ) ^ 2 * E.delta T ^ 2 * l1 ν)
    (fun n => ∑ j ∈ Finset.range n, γ ^ j) (fun n => Psi n γ) ?_ ?_ ?_ ?_ ?_ ?_ t hst htT).2
  · simp [PProd_self, Avec_self]
  · intro t hst _
    rw [PProd_succ E c hst, PProd_succ E θ hst, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      Avec_succ E θ ν hst, PMix_eq_add E c θ t]
    simp only [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.sub_vecMul, Matrix.smul_vecMul,
      smul_add, smul_sub]
    abel
  · intro t _ _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, sum_vecMul_Dk, mul_zero]
  · intro t hst htT
    rw [l1_smul]
    have h1 := l1_vecMul_Dk_le E T t htT
      (Matrix.vecMul ν (E.PProd c s t) - Matrix.vecMul ν (E.PProd θ s t))
    have h2 := (diff_bound E T γ hγ hmix θ c hθ hc ν s t hst htT.le).2
    calc |c - θ| * l1 (Matrix.vecMul
            (Matrix.vecMul ν (E.PProd c s t) - Matrix.vecMul ν (E.PProd θ s t)) (Dk E t))
        ≤ |c - θ| * (2 * E.delta T * (2 * E.delta T * |c - θ| * l1 ν
            * ∑ j ∈ Finset.range (t - s), γ ^ j)) :=
          mul_le_mul_of_nonneg_left
            (h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))) (abs_nonneg _)
      _ = 4 * (|c - θ| * |c - θ|) * E.delta T ^ 2 * l1 ν
            * ∑ j ∈ Finset.range (t - s), γ ^ j := by ring
      _ = 4 * (c - θ) ^ 2 * E.delta T ^ 2 * l1 ν * ∑ j ∈ Finset.range (t - s), γ ^ j := by
          rw [abs_mul_abs_self]; ring
  · exact Psi_zero γ
  · intro n
    exact Psi_succ n γ

/-- Endpoint expansion of the state distribution under the constant allocation `c` around the
experimental allocation `θ`, with window start `s ≤ t`:
`‖μ_c^t - (μ_θ^t + (c-θ) A^t)‖₁ ≤ γ^{t-s} · 2 δ |c-θ| G_s(γ) + 4 (c-θ)² δ² Ψ_{t-s}(γ)`,
where `A^t = A(μ_θ^s; s, t)`. -/
theorem endpoint_expansion (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (θ c : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (s t : ℕ) (hst : s ≤ t) (htT : t ≤ T) :
    l1 (E.stateDist c t - (E.stateDist θ t + (c - θ) • Avec E θ (E.stateDist θ s) s t))
      ≤ γ ^ (t - s) * (2 * E.delta T * |c - θ| * ∑ j ∈ Finset.range s, γ ^ j)
        + 4 * (c - θ) ^ 2 * E.delta T ^ 2 * Psi (t - s) γ := by
  have hδ := delta_nonneg E T
  obtain ⟨hw0, hw1⟩ := diff_bound E T γ hγ hmix θ c hθ hc E.ρ 0 s (Nat.zero_le s) (hst.trans htT)
  change (∑ x, (E.stateDist c s - E.stateDist θ s) x = 0) at hw0
  change l1 (E.stateDist c s - E.stateDist θ s) ≤ _ at hw1
  rw [l1_rho, mul_one, Nat.sub_zero] at hw1
  have hB := contraction E T γ hγ hmix (fun _ => c) (fun _ => hc) s t hst htT _ hw0
  have hR := rem_bound E T γ hγ hmix θ c hθ hc (E.stateDist θ s) s t hst htT
  have hμ : l1 (E.stateDist θ s) ≤ 1 := l1_stateDist_le E θ hθ s
  have hPsi : 0 ≤ Psi (t - s) γ := Psi_nonneg _ γ hγ
  have hdecomp : E.stateDist c t - (E.stateDist θ t + (c - θ) • Avec E θ (E.stateDist θ s) s t)
      = Matrix.vecMul (E.stateDist c s - E.stateDist θ s) (E.PProd c s t)
        + (Matrix.vecMul (E.stateDist θ s) (E.PProd c s t)
            - Matrix.vecMul (E.stateDist θ s) (E.PProd θ s t)
            - (c - θ) • Avec E θ (E.stateDist θ s) s t) := by
    rw [Matrix.sub_vecMul, stateDist_vecMul E c hst, stateDist_vecMul E θ hst]
    abel
  rw [hdecomp]
  calc l1 (Matrix.vecMul (E.stateDist c s - E.stateDist θ s) (E.PProd c s t)
          + (Matrix.vecMul (E.stateDist θ s) (E.PProd c s t)
            - Matrix.vecMul (E.stateDist θ s) (E.PProd θ s t)
            - (c - θ) • Avec E θ (E.stateDist θ s) s t))
      ≤ l1 (Matrix.vecMul (E.stateDist c s - E.stateDist θ s) (E.PProd c s t))
        + l1 (Matrix.vecMul (E.stateDist θ s) (E.PProd c s t)
            - Matrix.vecMul (E.stateDist θ s) (E.PProd θ s t)
            - (c - θ) • Avec E θ (E.stateDist θ s) s t) := l1_add_le _ _
    _ ≤ γ ^ (t - s) * l1 (E.stateDist c s - E.stateDist θ s)
        + 4 * (c - θ) ^ 2 * E.delta T ^ 2 * l1 (E.stateDist θ s) * Psi (t - s) γ :=
        add_le_add hB hR
    _ ≤ γ ^ (t - s) * (2 * E.delta T * |c - θ| * ∑ j ∈ Finset.range s, γ ^ j)
        + 4 * (c - θ) ^ 2 * E.delta T ^ 2 * Psi (t - s) γ := by
        refine add_le_add (mul_le_mul_of_nonneg_left hw1 (pow_nonneg hγ _)) ?_
        exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hμ) hPsi

/-! ### Per-time estimates with reward vectors -/

/-- Treatment-minus-control mean reward at time `t`, compared with its first-order expansion
around `θ` with window start `s ≤ t`, for arbitrary reward vectors bounded by `M`:
`|μ_1^t·r₁ - μ_0^t·r₀ - (μ_θ^t·(r₁-r₀) + A^t·((1-θ) r₁ + θ r₀))|
  ≤ 2 δ M γ^{t-s} G_s(γ) + 4 (θ² + (1-θ)²) δ² M Ψ_{t-s}(γ)`. -/
theorem gate_term_bound (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (r1 r0 : S → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (h1 : ∀ x, |r1 x| ≤ M) (h0 : ∀ x, |r0 x| ≤ M) (s t : ℕ) (hst : s ≤ t) (htT : t ≤ T) :
    |(E.stateDist 1 t ⬝ᵥ r1 - E.stateDist 0 t ⬝ᵥ r0)
        - (E.stateDist θ t ⬝ᵥ (r1 - r0)
            + Avec E θ (E.stateDist θ s) s t ⬝ᵥ ((1 - θ) • r1 + θ • r0))|
      ≤ 2 * E.delta T * M * γ ^ (t - s) * (∑ j ∈ Finset.range s, γ ^ j)
        + 4 * (θ ^ 2 + (1 - θ) ^ 2) * E.delta T ^ 2 * M * Psi (t - s) γ := by
  have e1 := endpoint_expansion E T γ hγ hmix θ 1 hθ ⟨zero_le_one, le_rfl⟩ s t hst htT
  have e0 := endpoint_expansion E T γ hγ hmix θ 0 hθ ⟨le_rfl, zero_le_one⟩ s t hst htT
  rw [abs_of_nonneg (by linarith [hθ.2] : (0 : ℝ) ≤ 1 - θ)] at e1
  have habs0 : |(0 : ℝ) - θ| = θ := by rw [zero_sub, abs_neg, abs_of_nonneg hθ.1]
  rw [habs0] at e0
  have hid : (E.stateDist 1 t ⬝ᵥ r1 - E.stateDist 0 t ⬝ᵥ r0)
        - (E.stateDist θ t ⬝ᵥ (r1 - r0)
            + Avec E θ (E.stateDist θ s) s t ⬝ᵥ ((1 - θ) • r1 + θ • r0))
      = (E.stateDist 1 t - (E.stateDist θ t + (1 - θ) • Avec E θ (E.stateDist θ s) s t)) ⬝ᵥ r1
        - (E.stateDist 0 t - (E.stateDist θ t + (0 - θ) • Avec E θ (E.stateDist θ s) s t)) ⬝ᵥ r0 := by
    simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    ring
  rw [hid]
  have b1 := abs_dotProduct_le
    (E.stateDist 1 t - (E.stateDist θ t + (1 - θ) • Avec E θ (E.stateDist θ s) s t)) r1 M h1
  have b0 := abs_dotProduct_le
    (E.stateDist 0 t - (E.stateDist θ t + (0 - θ) • Avec E θ (E.stateDist θ s) s t)) r0 M h0
  have c1 := mul_le_mul_of_nonneg_right e1 hM0
  have c0 := mul_le_mul_of_nonneg_right e0 hM0
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
      _ ≤ |a| + |-b| := abs_add_le _ _
      _ = |a| + |b| := by rw [abs_neg]
  refine (htri _ _).trans ?_
  refine (add_le_add (b1.trans c1) (b0.trans c0)).trans (le_of_eq ?_)
  ring

/-! ### Mean rewards in matrix form -/

theorem stateVec_eq (E : Env S) (q : ℕ → ℝ) (t : ℕ) :
    E.stateVec q t = Matrix.vecMul E.ρ (kprod E q 0 t) := by
  unfold Env.stateVec kprod
  rw [List.Ico.zero_bot]

theorem meanReward_const (E : Env S) (c : ℝ) (t : ℕ) :
    E.meanReward (fun _ => c) t = E.stateDist c t ⬝ᵥ E.rMix c := by
  unfold Env.meanReward
  rw [stateVec_eq]
  rfl

/-- If the allocation `q` equals `θ` at all times before `t`, the mean reward at time `t` is
`μ_θ^t · r_{q_t}`. -/
theorem meanReward_eq_of_agree_self (E : Env S) (q : ℕ → ℝ) (θ : ℝ) (t : ℕ)
    (hq : ∀ s, s < t → q s = θ) :
    E.meanReward q t = E.stateDist θ t ⬝ᵥ E.rMix (q t) := by
  unfold Env.meanReward
  rw [stateVec_eq,
    kprod_congr E (q := q) (q' := fun _ => θ) (a := 0) (b := t) (fun s _ hs => hq s hs)]
  rfl

/-- If the allocation `q` equals `θ` at all times before `t` except possibly at `u < t`, the
mean reward at time `t` is `μ_θ^u P_{q_u}^u Π_θ(u+1,t) · r_{q_t}`. -/
theorem meanReward_eq_of_agree (E : Env S) (q : ℕ → ℝ) (θ : ℝ) {u t : ℕ} (hut : u < t)
    (hq : ∀ s, s < t → s ≠ u → q s = θ) :
    E.meanReward q t
      = Matrix.vecMul (Matrix.vecMul (E.stateDist θ u) (E.PMix (q u) u)) (E.PProd θ (u + 1) t)
          ⬝ᵥ E.rMix (q t) := by
  unfold Env.meanReward
  rw [stateVec_eq, ← kprod_mul E _ (Nat.zero_le u) hut.le, kprod_cons E _ hut,
    kprod_congr E (q := q) (q' := fun _ => θ) (a := 0) (b := u)
      (fun s _ hs => hq s (by omega) (by omega)),
    kprod_congr E (q := q) (q' := fun _ => θ) (a := u + 1) (b := t)
      (fun s hs hs' => hq s hs' (by omega)),
    ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  rfl

theorem meanReward_update_self (E : Env S) (θ c : ℝ) (t : ℕ) :
    E.meanReward (Function.update (fun _ => θ) t c) t = E.stateDist θ t ⬝ᵥ E.rMix c := by
  rw [meanReward_eq_of_agree_self E _ θ t (fun s hs => Function.update_of_ne (by omega) _ _),
    Function.update_self]

/-- Summing the treatment-minus-control one-step perturbations over the window `[s, t)` gives
the first-order term: `∑_{u ∈ [s,t)} μ_θ^u (P_1^u - P_0^u) Π_θ(u+1,t) · r = A(μ_θ^s; s, t) · r`
for every reward vector `r`. -/
theorem window_sum_eq_Avec (E : Env S) (θ : ℝ) (r : S → ℝ) (s t : ℕ) :
    ∑ u ∈ Finset.Ico s t,
      (Matrix.vecMul (Matrix.vecMul (E.stateDist θ u) (E.PMix 1 u)) (E.PProd θ (u + 1) t) ⬝ᵥ r
        - Matrix.vecMul (Matrix.vecMul (E.stateDist θ u) (E.PMix 0 u)) (E.PProd θ (u + 1) t)
            ⬝ᵥ r)
      = Avec E θ (E.stateDist θ s) s t ⬝ᵥ r := by
  unfold Avec
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_Ico] at hu
  rw [← sub_dotProduct, ← Matrix.sub_vecMul, ← Matrix.vecMul_sub, PMix_one_sub_zero,
    stateDist_vecMul E θ hu.1]

/-- Assignment times `u` with `u < t ≤ u + k` are the window `[t - k, t)`. -/
theorem sum_fin_window_lt (T k t : ℕ) (ht : t < T) (f : ℕ → ℝ) :
    ∑ u : Fin T, (if (u : ℕ) < t ∧ t ≤ (u : ℕ) + k then f u else 0)
      = ∑ u ∈ Finset.Ico (t - k) t, f u := by
  refine (Fin.sum_univ_eq_sum_range (fun u => if u < t ∧ t ≤ u + k then f u else 0) T).trans ?_
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range T).filter (fun u => u < t ∧ t ≤ u + k)
      = Finset.Ico (t - k) t := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilter]

/-- Mean reward at time `t` when the allocation equals `θ` except for the value `c` at an earlier
time `u < t` and the value `d` at time `t` itself:
`μ_θ^u P_c^u Π_θ(u+1,t) · r_d`. -/
theorem meanReward_update_update (E : Env S) (θ c d : ℝ) {u t : ℕ} (hut : u < t) :
    E.meanReward (Function.update (Function.update (fun _ => θ) u c) t d) t
      = Matrix.vecMul (Matrix.vecMul (E.stateDist θ u) (E.PMix c u)) (E.PProd θ (u + 1) t)
          ⬝ᵥ E.rMix d := by
  have hne : u ≠ t := by omega
  rw [meanReward_eq_of_agree E _ θ hut (fun s hs hsu => by
      rw [Function.update_of_ne (by omega : s ≠ t), Function.update_of_ne hsu]),
    Function.update_self, Function.update_of_ne hne, Function.update_self]

/-- The inner sum over assignment times of the correction part of the mean of the RC estimator,
for a fixed reward time `t < T`: `A^t · ((1-θ) r₁ + θ r₀)` with window start `t - k`. -/
theorem rc_inner_sum (E : Env S) (T k : ℕ) (θ : ℝ) (t : ℕ) (ht : t < T) :
    ∑ u : Fin T, (if (u : ℕ) < t ∧ t ≤ (u : ℕ) + k then
        (E.meanReward (Function.update (Function.update (fun _ => θ) (u : ℕ) 1) t (1 - θ)) t
          - E.meanReward (Function.update (Function.update (fun _ => θ) (u : ℕ) 0) t (1 - θ)) t)
        else 0)
      = Avec E θ (E.stateDist θ (t - k)) (t - k) t ⬝ᵥ ((1 - θ) • E.r true + θ • E.r false) := by
  refine (sum_fin_window_lt T k t ht (fun u =>
    E.meanReward (Function.update (Function.update (fun _ => θ) u 1) t (1 - θ)) t
      - E.meanReward (Function.update (Function.update (fun _ => θ) u 0) t (1 - θ)) t)).trans ?_
  have hr : E.rMix (1 - θ) = (1 - θ) • E.r true + θ • E.r false := by
    rw [rMix_eq, sub_sub_cancel]
  rw [← hr, ← window_sum_eq_Avec]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_Ico] at hu
  rw [meanReward_update_update E θ 1 (1 - θ) hu.2, meanReward_update_update E θ 0 (1 - θ) hu.2]

end Products

end RCBias

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M : ℝ)
    (hT : 0 < T) (hk : k ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 ≤ γ)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M) :
    |(∫ ω, rcEst θ T k ω ∂(E.expLaw T θ)) - E.gate T|
      ≤ (1 / (T : ℝ)) * ∑ t : Fin T,
          (2 * E.delta T * M * γ ^ (min (t : ℕ) k) * (∑ j ∈ Finset.range ((t : ℕ) - k), γ ^ j)
            + 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M * Psi (min (t : ℕ) k) γ) := by
  classical
  have hθ : 0 ≤ θ ∧ θ ≤ 1 := ⟨hθ0.le, hθ1.le⟩
  have hr : ∀ z x, |E.r z x| ≤ M := RCBias.abs_r_le E M hM
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := E.ρ_sum
    simp at h1
  obtain ⟨x0⟩ := hne
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hr true x0)
  rw [TPG.integral_rcEst E T k θ M hθ0 hθ1 hM, TPG.gate_eq_meanReward E T M hM]
  have hcomm : (∑ u : Fin T,
        ((E.meanReward (Function.update (fun _ => θ) (u : ℕ) 1) (u : ℕ)
            - E.meanReward (Function.update (fun _ => θ) (u : ℕ) 0) (u : ℕ))
          + ∑ t : Fin T,
              if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
                (E.meanReward
                    (Function.update (Function.update (fun _ => θ) (u : ℕ) 1) (t : ℕ) (1 - θ))
                    (t : ℕ)
                  - E.meanReward
                    (Function.update (Function.update (fun _ => θ) (u : ℕ) 0) (t : ℕ) (1 - θ))
                    (t : ℕ))
              else 0))
      = ∑ t : Fin T, (E.stateDist θ t ⬝ᵥ (E.r true - E.r false)
          + RCBias.Avec E θ (E.stateDist θ ((t : ℕ) - k)) ((t : ℕ) - k) t
              ⬝ᵥ ((1 - θ) • E.r true + θ • E.r false)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [RCBias.meanReward_update_self, RCBias.meanReward_update_self, RCBias.rMix_one,
        RCBias.rMix_zero, ← dotProduct_sub]
    · refine Eq.trans Finset.sum_comm ?_
      exact Finset.sum_congr rfl fun t _ => RCBias.rc_inner_sum E T k θ t t.2
  rw [hcomm, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (T : ℝ))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [RCBias.meanReward_const, RCBias.meanReward_const, RCBias.rMix_one, RCBias.rMix_zero,
    abs_sub_comm]
  have hmin : min (t : ℕ) k = (t : ℕ) - ((t : ℕ) - k) := by omega
  rw [hmin]
  exact RCBias.gate_term_bound E T γ hγ0 hmix θ hθ (E.r true) (E.r false) M hM0 (hr true)
    (hr false) ((t : ℕ) - k) t (Nat.sub_le _ _) t.2.le
