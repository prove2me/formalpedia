-- Prove2me | solution 1 for RobustSAA.Univariate.ks_sq_le_ad
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:27:52.651175+00:00
-- url     : https://prove2.me/submissions/3e4a469e-1e06-4774-a70d-450306647ed7

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting
import Theorems.Thm_RobustSAA_Univariate_ks_sq_le_cvm

open Filter MeasureTheory RobustSAA.Univariate Set

namespace RSAA3AD

/-- `H p x = Φ_p(x) − Ψ_p(x)`, the antiderivative of `(p − x)²/(x(1−x)) − (p − x)²`. -/
noncomputable def H (p x : ℝ) : ℝ :=
  -x + p ^ 2 * Real.log x - (1 - p) ^ 2 * Real.log (1 - x) + (p - x) ^ 3 / 3

lemma H_hasDerivAt (p x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (H p) (-1 + p ^ 2 / x + (1 - p) ^ 2 / (1 - x) - (p - x) ^ 2) x := by
  have h0 : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id' x).neg
  have h1 : HasDerivAt (fun y : ℝ => p ^ 2 * Real.log y) (p ^ 2 * x⁻¹) x :=
    (Real.hasDerivAt_log hx0.ne').const_mul _
  have h2 : HasDerivAt (fun y : ℝ => (1 - p) ^ 2 * Real.log (1 - y))
      ((1 - p) ^ 2 * ((-1) / (1 - x))) x :=
    (((hasDerivAt_id' x).const_sub 1).log (by linarith)).const_mul _
  have h3 : HasDerivAt (fun y : ℝ => (p - y) ^ 3 / 3)
      (((3 : ℕ) : ℝ) * (p - x) ^ (3 - 1) * (-1) / 3) x :=
    (((hasDerivAt_id' x).const_sub p).pow 3).div_const 3
  have := ((h0.add h1).sub h2).add h3
  refine this.congr_deriv ?_
  have : (1 - x) ≠ 0 := by linarith
  field_simp
  ring

lemma deriv_nonneg (p x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    0 ≤ -1 + p ^ 2 / x + (1 - p) ^ 2 / (1 - x) - (p - x) ^ 2 := by
  have hx : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have e : -1 + p ^ 2 / x + (1 - p) ^ 2 / (1 - x) = (p - x) ^ 2 / (x * (1 - x)) := by
    have : (1 - x) ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  have : (p - x) ^ 2 ≤ (p - x) ^ 2 / (x * (1 - x)) :=
    le_div_self (sq_nonneg _) hx (by nlinarith)
  linarith

lemma H_mono (p a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1) (hA : a = 0 → p = 0)
    (hB : b = 1 → p = 1) : H p a ≤ H p b := by
  rcases eq_or_lt_of_le hab with h | hlt
  · rw [h]
  have hcont : ContinuousOn (H p) (Icc a b) := by
    have c1 : ContinuousOn (fun x : ℝ => p ^ 2 * Real.log x) (Icc a b) := by
      rcases eq_or_lt_of_le ha with h0 | h0
      · have hp : p = 0 := hA h0.symm
        have : (fun x : ℝ => p ^ 2 * Real.log x) = fun _ => 0 := by funext x; rw [hp]; ring
        rw [this]; exact continuousOn_const
      · exact continuousOn_const.mul (Real.continuousOn_log.mono (fun x hx => by
          simp only [mem_compl_iff, mem_singleton_iff]; have := hx.1; intro h; linarith))
    have c2 : ContinuousOn (fun x : ℝ => (1 - p) ^ 2 * Real.log (1 - x)) (Icc a b) := by
      rcases eq_or_lt_of_le hb with h1 | h1
      · have hp : p = 1 := hB h1
        have : (fun x : ℝ => (1 - p) ^ 2 * Real.log (1 - x)) = fun _ => 0 := by
          funext x; rw [hp]; ring
        rw [this]; exact continuousOn_const
      · refine continuousOn_const.mul (ContinuousOn.log (continuousOn_const.sub continuousOn_id)
          (fun x hx => ?_))
        have := hx.2; show (1:ℝ) - x ≠ 0; linarith
    have c3 : ContinuousOn (fun x : ℝ => (p - x) ^ 3 / 3) (Icc a b) :=
      ((continuousOn_const.sub continuousOn_id).pow 3).div_const 3
    have : H p = fun x => -x + p ^ 2 * Real.log x - (1 - p) ^ 2 * Real.log (1 - x) +
        (p - x) ^ 3 / 3 := rfl
    rw [this]
    exact ((continuousOn_id.neg.add c1).sub c2).add c3
  have hmono : MonotoneOn (H p) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont
    · rw [interior_Icc]
      intro x hx
      exact (H_hasDerivAt p x (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt
        |>.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(H_hasDerivAt p x (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      exact deriv_nonneg p x (by linarith [hx.1]) (by linarith [hx.2])
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Abel summation. -/
lemma abel (c f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), c k * (f (k + 1) - f k) =
      c n * f (n + 1) - c 0 * f 0 - ∑ i ∈ Finset.range n, (c (i + 1) - c i) * f (i + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

lemma diag (G : ℕ → ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (G k k - G k (k + 1)) =
      G 0 0 - G n (n + 1) + ∑ i ∈ Finset.range n, (G (i + 1) (i + 1) - G i (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

end RSAA3AD

open RSAA3AD

/-- `A_N² ≥ W_N²` when all `F₀(ξ^(i)) ∈ (0,1)`. -/
lemma adSq_ge_cvm {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ)
    (hu : ∀ i, 0 < u F₀ s i ∧ u F₀ s i < 1) : cvmStat F₀ s ^ 2 ≤ adSq F₀ s := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : Monotone (u F₀ s) :=
    (ProbabilityTheory.monotone_cdf _).comp (Tuple.monotone_sort s)
  -- ℕ-indexed data
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun n => if h : n < N then u F₀ s ⟨n, h⟩ else 1 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, v = fun n => if n = 0 then 0 else w (n - 1) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℝ, p = fun k : ℕ => (k : ℝ) / N := ⟨_, rfl⟩
  have hwi : ∀ i : Fin N, w i = u F₀ s i := by intro i; rw [hw]; simp [i.isLt]
  have hv0 : v 0 = 0 := by rw [hv]; simp
  have hvs : ∀ n, v (n + 1) = w n := by intro n; rw [hv]; simp
  have hvN : v (N + 1) = 1 := by rw [hvs, hw]; simp
  have hw01 : ∀ n < N, 0 < w n ∧ w n < 1 := by
    intro n hn; rw [hw]; simp only [hn, dif_pos]; exact hu _
  have hp0 : p 0 = 0 := by rw [hp]; simp
  have hpN : p N = 1 := by rw [hp]; simp [hNr.ne']
  -- termwise nonnegativity
  have hterm : ∀ k ∈ Finset.range (N + 1), 0 ≤ H (p k) (v (k + 1)) - H (p k) (v k) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [sub_nonneg]
    apply H_mono
    · -- v k ≤ v (k+1)
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; rw [hv0, hvs]
        rcases Nat.eq_zero_or_pos N with h | h
        · omega
        · exact (hw01 0 h).1.le
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hvs, hvs]
        rcases lt_or_ge (j + 1) N with h | h
        · rw [hw]; simp only [h, show j < N by omega, dif_pos]
          exact hmono (show (⟨j, by omega⟩ : Fin N) ≤ ⟨j + 1, h⟩ from Nat.le_succ j)
        · have : j + 1 = N := by omega
          rw [this, hw]; simp only [show j < N by omega, dif_pos, lt_irrefl, dif_neg,
            not_false_eq_true]
          exact (hu _).2.le
    · rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; rw [hv0]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hvs]; exact (hw01 j (by omega)).1.le
    · rcases lt_or_ge k N with h | h
      · rw [hvs]; exact (hw01 k h).2.le
      · have : k = N := by omega
        rw [this, hvN]
    · intro h0
      rcases Nat.eq_zero_or_pos k with hk0 | hpos
      · rw [hk0, hp0]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hvs] at h0
        exact absurd h0 (hw01 j (by omega)).1.ne'
    · intro h1
      rcases lt_or_ge k N with h | h
      · rw [hvs] at h1
        exact absurd h1 (hw01 k h).2.ne
      · have : k = N := by omega
        rw [this, hpN]
  have hsum := Finset.sum_nonneg hterm
  -- identity for the AD part
  have hAD : ∑ k ∈ Finset.range (N + 1), (H (p k) (v (k + 1)) - H (p k) (v k)) =
      adSq F₀ s - cvmStat F₀ s ^ 2 := by
    have split : ∀ k, H (p k) (v (k + 1)) - H (p k) (v k) =
        -(v (k + 1) - v k) + (p k) ^ 2 * (Real.log (v (k + 1)) - Real.log (v k))
        - (1 - p k) ^ 2 * (Real.log (1 - v (k + 1)) - Real.log (1 - v k))
        - ((p k - v (k + 1)) ^ 3 * (-1 / 3) - (p k - v k) ^ 3 * (-1 / 3)) := by
      intro k; simp only [H]; ring
    simp_rw [split]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_range_sub (fun n => v n)]
    rw [abel (fun k => (p k) ^ 2) (fun n => Real.log (v n)) N,
      abel (fun k => (1 - p k) ^ 2) (fun n => Real.log (1 - v n)) N]
    have hcub := diag (fun k n => (p k - v n) ^ 3 * (-1 / 3)) N
    have hcub' : ∑ k ∈ Finset.range (N + 1),
        ((p k - v (k + 1)) ^ 3 * (-1 / 3) - (p k - v k) ^ 3 * (-1 / 3)) =
        -∑ k ∈ Finset.range (N + 1), ((p k - v k) ^ 3 * (-1 / 3) -
          (p k - v (k + 1)) ^ 3 * (-1 / 3)) := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext k; ring
    rw [hcub', hcub]
    simp only [hv0, hvN, hp0, hpN, hvs, Real.log_zero, Real.log_one, sub_zero, sub_self,
      mul_zero, zero_mul]
    -- now compare with the definitions
    have hpd : ∀ i : ℕ, p (i + 1) ^ 2 - p i ^ 2 = (2 * (i : ℝ) + 1) / (N : ℝ) ^ 2 := by
      intro i; rw [hp]; push_cast; field_simp; ring
    have hqd : ∀ i : ℕ, (1 - p (i + 1)) ^ 2 - (1 - p i) ^ 2 =
        -((2 * ((N : ℝ) - 1 - i) + 1) / (N : ℝ) ^ 2) := by
      intro i; rw [hp]; push_cast; field_simp; ring
    have hcd : ∀ i : ℕ, (p (i + 1) - w i) ^ 3 * (-1 / 3) - (p i - w i) ^ 3 * (-1 / 3) =
        -((1 / (N : ℝ)) * ((2 * (i : ℝ) + 1) / (2 * N) - w i) ^ 2 + 1 / (12 * (N : ℝ) ^ 3)) := by
      intro i; rw [hp]; push_cast; field_simp; ring
    simp only [hpd, hqd, hcd]
    -- definitions as sums over range N
    have hAD' : adSq F₀ s = -1 - ∑ i ∈ Finset.range N, (2 * (i : ℝ) + 1) / (N : ℝ) ^ 2 *
        Real.log (w i) - ∑ i ∈ Finset.range N, (2 * ((N : ℝ) - 1 - i) + 1) / (N : ℝ) ^ 2 *
        Real.log (1 - w i) := by
      unfold adSq
      rw [Finset.sum_congr rfl (fun i _ => mul_add _ _ _), Finset.sum_add_distrib]
      have e1 : ∑ i : Fin N, (2 * ((i : ℕ) + 1 : ℝ) - 1) / (N : ℝ) ^ 2 * Real.log (u F₀ s i) =
          ∑ i ∈ Finset.range N, (2 * (i : ℝ) + 1) / (N : ℝ) ^ 2 * Real.log (w i) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => (2 * (i : ℝ) + 1) / (N : ℝ) ^ 2 *
          Real.log (w i)) N]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hwi]; ring_nf
      have e2 : ∑ i : Fin N, (2 * ((i : ℕ) + 1 : ℝ) - 1) / (N : ℝ) ^ 2 *
          Real.log (1 - u F₀ s (Fin.rev i)) =
          ∑ i ∈ Finset.range N, (2 * ((N : ℝ) - 1 - i) + 1) / (N : ℝ) ^ 2 *
            Real.log (1 - w i) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => (2 * ((N : ℝ) - 1 - i) + 1) / (N : ℝ) ^ 2 *
          Real.log (1 - w i)) N]
        rw [← Equiv.sum_comp Fin.revPerm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [Fin.revPerm_apply, Fin.rev_rev]
        rw [hwi]
        congr 1
        rw [Fin.val_rev]
        have : ((N - (i + 1) : ℕ) : ℝ) = (N : ℝ) - (i + 1) := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; ring
      rw [e1, e2]; ring
    have hcvm' : cvmStat F₀ s ^ 2 = 1 / (12 * (N : ℝ) ^ 2) +
        (1 / (N : ℝ)) * ∑ i ∈ Finset.range N, ((2 * (i : ℝ) + 1) / (2 * N) - w i) ^ 2 := by
      unfold cvmStat
      rw [Real.sq_sqrt (by positivity)]
      congr 2
      rw [← Fin.sum_univ_eq_sum_range (fun i => ((2 * (i : ℝ) + 1) / (2 * N) - w i) ^ 2) N]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hwi]; ring_nf
    rw [hAD', hcvm']
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, neg_mul, ← Finset.mul_sum]
    have e3 : (N : ℝ) * (1 / (12 * (N : ℝ) ^ 3)) = 1 / (12 * (N : ℝ) ^ 2) := by
      field_simp
    rw [e3]
    ring
  linarith

theorem solution {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ)
    (hu : ∀ i, 0 < u F₀ s i ∧ u F₀ s i < 1) :
    ksStat F₀ s ^ 2 ≤
      max (1 / Real.sqrt N + 3 / (2 * N))
        (Real.sqrt N * adSq F₀ s + 2 / Real.sqrt N) := by
  refine le_trans (ks_sq_le_cvm hN F₀ s) (max_le_max le_rfl ?_)
  have := adSq_ge_cvm hN F₀ s hu
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left this hs]
