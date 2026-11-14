-- Prove2me | solution 1 for StabilityDichotomies.Solvability.shared_mask_aggregate_antitone_transport_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:37:21.344229+00:00
-- url     : https://prove2.me/submissions/3195b2cf-3348-4327-ab85-02c9b1fef154

import Theorems.Thm_StabilityDichotomies_Solvability_shared_mask_integrated_transport_bound
import Theorems.Thm_StabilityDichotomies_Approximability_integrated_monotone_hamming_influences
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Approximability

theorem solution (m : ℕ) {V : Type} [Fintype V]
    (out : (Fin m → Bool) → V → Bool) (hanti : Antitone out) (B ε : ℝ)
    (hbound : ∀ mask, (∑ v : V, if !out mask v then (1 : ℝ) else 0) ≤ B)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (μ : PMF (V → Bool)) (ν : Fin m → PMF (V → Bool))
    (hμ : ∀ x, (μ x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask * (if out mask = x then 1 else 0))
    (hν : ∀ i x, (ν i x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask *
        (if out (Function.update mask i false) = x then 1 else 0)) :
    (∑ i, wasserstein μ (ν i)) ≤ B * ε⁻¹ := by
  let D : Fin m → ℝ → ℝ := fun i p =>
    p * ∑ mask : Fin m → Bool, retentionWeight p mask *
      (hammingDist (out (Function.update mask i true)) (out (Function.update mask i false)) : ℝ)
  have hc (mask : Fin m → Bool) : Continuous (fun p : ℝ => retentionWeight p mask) := by
    unfold retentionWeight
    apply continuous_finsetProd
    intro j hj
    cases hm : mask j <;> simp only [hm, Bool.false_eq_true, ↓reduceIte]
    · exact continuous_const.sub continuous_id
    · exact continuous_id
  have hD (i : Fin m) : Continuous (D i) := by
    unfold D
    fun_prop
  let out' : (Fin m → Bool) → V → Bool := fun mask v => !(out mask v)
  have hmono : Monotone out' := by
    intro a b hab v
    have h := hanti hab v
    cases ha : out a v <;> cases hb : out b v <;> simp_all [out']
  have hbound' : ∀ mask, (∑ v : V, if out' mask v then (1 : ℝ) else 0) ≤ B := hbound
  have hdist (a b : Fin m → Bool) : hammingDist (out' a) (out' b) = hammingDist (out a) (out b) := by
    exact hammingDist_comp (fun _ : V => Bool.not) (fun _ => Bool.not_injective)
  calc
    _ ≤ ∑ i : Fin m, ε⁻¹ * ∫ p in (1-ε)..1, D i p := by
      apply Finset.sum_le_sum
      intro i hi
      exact shared_mask_integrated_transport_bound m out i ε hε hε1 μ (ν i) hμ (hν i)
    _ = ε⁻¹ * ∫ p in (1-ε)..1, p * ∑ i : Fin m, ∑ mask : Fin m → Bool,
      retentionWeight p mask *
        (hammingDist (out (Function.update mask i true)) (out (Function.update mask i false)) : ℝ) := by
      rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun i hi => (hD i).intervalIntegrable _ _)]
      congr 1
      apply intervalIntegral.integral_congr
      intro p hp
      simp [D, Finset.mul_sum]
    _ ≤ ε⁻¹ * B := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hε))
      have hi := integrated_monotone_hamming_influences out' hmono B ε hbound' (le_of_lt hε) hε1
      simp_rw [hdist] at hi
      convert hi using 1 <;> try rfl
      apply intervalIntegral.integral_congr
      intro p hp
      simp only [retentionWeight]
      congr 1
      apply Finset.sum_congr
      · ext i; simp
      · intro i hi
        apply Finset.sum_congr
        · ext x; simp
        · intro x hx
          congr 4 <;> funext j <;> by_cases hj : j = i <;> simp [Function.update, hj]
    _ = B * ε⁻¹ := mul_comm _ _
