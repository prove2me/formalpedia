-- Prove2me | solution 1 for UnderstandingML.chaining_corollary
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T17:40:47.707535+00:00
-- url     : https://prove2.me/submissions/324e8229-f4bd-4cbe-b34e-e7bfa65075a6

import Theorems.Thm_UnderstandingML_dudley_chaining
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory

namespace UnderstandingML.ChainingCorollaryAux

/-- `∑_{k=1}^M 2^{-k} (α + β k) = α (1 − 2^{-M}) + β (2 − (M + 2) 2^{-M})`. -/
lemma sum_geom_linear (α β : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (2 : ℝ)⁻¹ ^ k * (α + β * k) =
      α * (1 - (2 : ℝ)⁻¹ ^ M) + β * (2 - (M + 2) * (2 : ℝ)⁻¹ ^ M) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

lemma sum_geom_linear_le {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (2 : ℝ)⁻¹ ^ k * (α + β * k) ≤ α + 2 * β := by
  rw [sum_geom_linear]
  have h1 : 0 ≤ (2 : ℝ)⁻¹ ^ M := by positivity
  have h2 : 0 ≤ ((M : ℝ) + 2) * (2 : ℝ)⁻¹ ^ M := by positivity
  nlinarith [mul_nonneg hα h1, mul_nonneg hβ h2]

end UnderstandingML.ChainingCorollaryAux

open UnderstandingML UnderstandingML.ChainingCorollaryAux in
theorem solution {m : ℕ} (hm : 0 < m) (A : Set (Fin m → ℝ)) (hA : A.Nonempty) (c : ℝ)
    (abar : Fin m → ℝ) (hc : ∀ a ∈ A, eucNorm (a - abar) ≤ c) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β)
    (hN : ∀ k : ℕ, 1 ≤ k →
      Real.sqrt (Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat)) ≤ α + β * k) :
    rademacher A ≤ 6 * c / m * (α + 2 * β) := by
  obtain ⟨a₀, ha₀⟩ := hA
  have hc0 : 0 ≤ c := (Real.sqrt_nonneg _).trans (hc a₀ ha₀)
  -- Lemma 27.4 at every depth `M ≥ 1`, with the sum bounded by `α + 2β`
  have hM : ∀ M : ℕ, rademacher A ≤ c * (2 : ℝ)⁻¹ ^ (M + 1) / Real.sqrt m +
      6 * c / m * (α + 2 * β) := by
    intro M
    refine (dudley_chaining hm A ⟨a₀, ha₀⟩ c abar hc (M + 1) (Nat.succ_pos M)).trans ?_
    gcongr
    calc ∑ k ∈ Finset.Icc 1 (M + 1),
          (2 : ℝ)⁻¹ ^ k * Real.sqrt (Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat))
        ≤ ∑ k ∈ Finset.Icc 1 (M + 1), (2 : ℝ)⁻¹ ^ k * (α + β * k) := by
          refine Finset.sum_le_sum (fun k hk ↦ ?_)
          gcongr
          exact hN k (Finset.mem_Icc.1 hk).1
      _ ≤ α + 2 * β := sum_geom_linear_le hα.le hβ.le _
  -- let `M → ∞`
  have hlim : Filter.Tendsto (fun M : ℕ ↦ c * (2 : ℝ)⁻¹ ^ (M + 1) / Real.sqrt m +
      6 * c / m * (α + 2 * β)) Filter.atTop (nhds (0 + 6 * c / m * (α + 2 * β))) := by
    refine Filter.Tendsto.add ?_ tendsto_const_nhds
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := (h.const_mul c).div_const (Real.sqrt m)
    simpa using h2
  rw [zero_add] at hlim
  exact ge_of_tendsto' hlim hM
