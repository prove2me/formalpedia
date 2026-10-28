-- Prove2me | solution 1 for ResidualsDRO.Wass.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:24:57.328196+00:00
-- url     : https://prove2.me/submissions/fbd4da4b-7fb0-490f-91cf-a90970832e5c

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_ResidualsDRO_Wass_Radius
open MeasureTheory

namespace Aux_RDRO6
open ResidualsDRO.Wass

lemma pm_le {n : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p) (c : ℝ) (hc : 0 ≤ c) (b v : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ c + b i) :
    powerMean p v ≤ c + powerMean p b := by
  have hp0 : 0 < p := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold powerMean
  have h1 : ((n : ℝ)⁻¹ * ∑ i, v i ^ p) ^ (1 / p) ≤ ((n : ℝ)⁻¹ * ∑ i, (c + b i) ^ p) ^ (1 / p) := by
    apply Real.rpow_le_rpow
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hv i).1 _))
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (hv i).1 (hv i).2 hp0.le)
    · positivity
  have hS : 0 ≤ ∑ i, (c + b i) ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (by linarith [hb i]) _)
  have hSb : 0 ≤ ∑ i, b i ^ p := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hb i) _)
  have hmink := Real.Lp_add_le_of_nonneg (s := Finset.univ) (f := fun _ : Fin n => c)
    (g := b) hp (fun i _ => hc) (fun i _ => hb i)
  have hconst : ∑ _i : Fin n, c ^ p = (n : ℝ) * c ^ p := by simp
  rw [hconst] at hmink
  have e1 : ((n : ℝ)⁻¹) ^ (1 / p) * ((n : ℝ) * c ^ p) ^ (1 / p) = c := by
    rw [← Real.mul_rpow (by positivity) (by positivity), ← mul_assoc, inv_mul_cancel₀ hnr.ne',
      one_mul, one_div, Real.rpow_rpow_inv hc hp0.ne']
  have e2 : ((n : ℝ)⁻¹) ^ (1 / p) * (∑ i, b i ^ p) ^ (1 / p) =
      ((n : ℝ)⁻¹ * ∑ i, b i ^ p) ^ (1 / p) := (Real.mul_rpow (by positivity) hSb).symm
  calc ((n : ℝ)⁻¹ * ∑ i, v i ^ p) ^ (1 / p)
      ≤ ((n : ℝ)⁻¹ * ∑ i, (c + b i) ^ p) ^ (1 / p) := h1
    _ = ((n : ℝ)⁻¹) ^ (1 / p) * (∑ i, (c + b i) ^ p) ^ (1 / p) :=
        Real.mul_rpow (by positivity) hS
    _ ≤ ((n : ℝ)⁻¹) ^ (1 / p) * (((n : ℝ) * c ^ p) ^ (1 / p) + (∑ i, b i ^ p) ^ (1 / p)) :=
        mul_le_mul_of_nonneg_left hmink (by positivity)
    _ = c + ((n : ℝ)⁻¹ * ∑ i, b i ^ p) ^ (1 / p) := by rw [mul_add, e1, e2]

end Aux_RDRO6

open ResidualsDRO.Wass in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {dx dy n : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p)
    (fstar : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (fhat : Ω → EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → Ω → EuclideanSpace ℝ (Fin dx)) (eps : Fin n → Ω → EuclideanSpace ℝ (Fin dy))
    (x : EuclideanSpace ℝ (Fin dx)) (κ : ℝ → ℝ) (hA2 : Assumption2 P fstar fhat xs p x κ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    P {ω | 2 * κ (α / 4) <
        powerMean p (fun i => ‖epsTilde fstar (fhat ω) (fun j => xs j ω) (fun j => eps j ω) x i‖)} ≤
      ENNReal.ofReal (α / 2) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hκ, hA, hB⟩ := hA2 (α / 4) (by linarith) (by linarith)
  set k := κ (α / 4) with hk
  have hsub : {ω | 2 * k < powerMean p
      (fun i => ‖epsTilde fstar (fhat ω) (fun j => xs j ω) (fun j => eps j ω) x i‖)} ⊆
      {ω | k ^ p < ‖fstar x - fhat ω x‖ ^ p} ∪
      {ω | k ^ p < (n : ℝ)⁻¹ * ∑ i, ‖fstar (xs i ω) - fhat ω (xs i ω)‖ ^ p} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hc
    obtain ⟨c1, c2⟩ := hc
    have ha : ‖fstar x - fhat ω x‖ ≤ k :=
      (Real.rpow_le_rpow_iff (norm_nonneg _) hκ.le hp0).mp c1
    have hM0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i, ‖fstar (xs i ω) - fhat ω (xs i ω)‖ ^ p :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))
    have hb : powerMean p (fun i => ‖fstar (xs i ω) - fhat ω (xs i ω)‖) ≤ k := by
      unfold powerMean
      calc ((n : ℝ)⁻¹ * ∑ i, ‖fstar (xs i ω) - fhat ω (xs i ω)‖ ^ p) ^ (1 / p)
          ≤ (k ^ p) ^ (1 / p) := Real.rpow_le_rpow hM0 c2 (by positivity)
        _ = k := by rw [one_div, Real.rpow_rpow_inv hκ.le hp0.ne']
    have hpm := Aux_RDRO6.pm_le hn p hp ‖fstar x - fhat ω x‖ (norm_nonneg _)
      (fun i => ‖fstar (xs i ω) - fhat ω (xs i ω)‖)
      (fun i => ‖epsTilde fstar (fhat ω) (fun j => xs j ω) (fun j => eps j ω) x i‖)
      (fun i => norm_nonneg _) (fun i => ⟨norm_nonneg _, by
        have e : epsTilde fstar (fhat ω) (fun j => xs j ω) (fun j => eps j ω) x i =
            (fhat ω x - fstar x) + (fstar (xs i ω) - fhat ω (xs i ω)) := by
          unfold epsTilde ResidualsDRO.Wass.residual; abel
        rw [e, norm_sub_rev (fstar x)]
        exact norm_add_le _ _⟩)
    have : powerMean p
        (fun i => ‖epsTilde fstar (fhat ω) (fun j => xs j ω) (fun j => eps j ω) x i‖) ≤ 2 * k := by
      linarith
    exact absurd hω (not_lt.mpr this)
  calc P _ ≤ P ({ω | k ^ p < ‖fstar x - fhat ω x‖ ^ p} ∪
        {ω | k ^ p < (n : ℝ)⁻¹ * ∑ i, ‖fstar (xs i ω) - fhat ω (xs i ω)‖ ^ p}) := measure_mono hsub
    _ ≤ P {ω | k ^ p < ‖fstar x - fhat ω x‖ ^ p} +
        P {ω | k ^ p < (n : ℝ)⁻¹ * ∑ i, ‖fstar (xs i ω) - fhat ω (xs i ω)‖ ^ p} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (α / 4) + ENNReal.ofReal (α / 4) := add_le_add hA hB
    _ = ENNReal.ofReal (α / 2) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
