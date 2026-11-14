-- Prove2me | solution 1 for StabilityDichotomies.Solvability.shared_mask_integrated_transport_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:26:44.4366+00:00
-- url     : https://prove2.me/submissions/0f820603-39bc-460c-a213-5a899b42aff2

import Theorems.Thm_StabilityDichotomies_Solvability_shared_seed_for_uniform_bernoulli_mixture
import Theorems.Thm_StabilityDichotomies_Solvability_wasserstein_le_shared_seed_cost
import Theorems.Thm_StabilityDichotomies_Approximability_fixed_p_deletion_shared_mask_cost
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Approximability

theorem solution (m : ℕ) {V : Type} [Fintype V]
    (out : (Fin m → Bool) → V → Bool) (i : Fin m) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (μ ν : PMF (V → Bool))
    (hμ : ∀ x, (μ x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask * (if out mask = x then 1 else 0))
    (hν : ∀ x, (ν x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask *
        (if out (Function.update mask i false) = x then 1 else 0)) :
    wasserstein μ ν ≤ ε⁻¹ * ∫ p in (1-ε)..1,
      p * ∑ mask : Fin m → Bool, retentionWeight p mask *
        (hammingDist (out (Function.update mask i true)) (out (Function.update mask i false)) : ℝ) := by
  obtain ⟨ρ,hρ⟩ := shared_seed_for_uniform_bernoulli_mixture m ε hε hε1
  have hμ' : μ = ρ.map out := by
    apply PMF.ext
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top x) ((ρ.map out).apply_ne_top x)).mp
    refine (hμ x).trans ?_
    simpa using (hρ (V → Bool) out x).symm
  have hν' : ν = ρ.map (fun mask => out (Function.update mask i false)) := by
    apply PMF.ext
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' (ν.apply_ne_top x)
      ((ρ.map (fun mask => out (Function.update mask i false))).apply_ne_top x)).mp
    refine (hν x).trans ?_
    simpa using (hρ (V → Bool) (fun mask => out (Function.update mask i false)) x).symm
  have hρpoint (mask : Fin m → Bool) : (ρ mask).toReal = ε⁻¹ *
      ∫ p in (1-ε)..1, retentionWeight p mask := by
    have h := hρ (Fin m → Bool) id mask
    rw [PMF.map_id] at h
    simpa using h
  rw [hμ',hν']
  refine (wasserstein_le_shared_seed_cost ρ out (fun mask => out (Function.update mask i false))).trans ?_
  have hc (mask : Fin m → Bool) : Continuous (fun p : ℝ => retentionWeight p mask) := by
    unfold retentionWeight
    apply continuous_finsetProd
    intro j hj
    cases hm : mask j <;> simp only [hm, Bool.false_eq_true, ↓reduceIte]
    · exact continuous_const.sub continuous_id
    · exact continuous_id
  simp_rw [hρpoint, mul_assoc, ← intervalIntegral.integral_mul_const]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum]
  · apply le_of_eq
    congr 1
    apply intervalIntegral.integral_congr
    intro p hp
    simp only [hammingCost, retentionWeight]
    convert fixed_p_deletion_shared_mask_cost out p i using 1
    · apply Finset.sum_congr
      · ext x; simp
      · intro x hx
        congr 4
        funext j
        by_cases hj : j = i <;> simp [Function.update, hj]
    · congr 1
      apply Finset.sum_congr
      · ext x; simp
      · intro x hx
        congr 4 <;> funext j <;> by_cases hj : j = i <;> simp [Function.update, hj]
  · intro mask hm
    have h : Continuous (fun p : ℝ => retentionWeight p mask *
        hammingCost (out mask) (out (Function.update mask i false))) := by fun_prop
    exact h.intervalIntegrable _ _
