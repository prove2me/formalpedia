-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P36.rains_crossEntropy_objective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:03:34.913313+00:00
-- url     : https://prove2.me/submissions/f46c8f68-b9de-4b4b-89a9-99d7f778954b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- the affine order isomorphism x ↦ c*x + d of EReal, c > 0 -/
def h54d_aff (c d : ℝ) (hc : 0 < c) : EReal ≃o EReal :=
  have h1 : ((c : EReal) * ((c⁻¹ : ℝ) : EReal)) = 1 := by
    rw [← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one]
  have h2 : (((c⁻¹ : ℝ) : EReal) * (c : EReal)) = 1 := by
    rw [← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one]
  have hc0 : (0 : EReal) ≤ (c : EReal) := by exact_mod_cast hc.le
  have hc1 : (0 : EReal) ≤ ((c⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_nonneg.mpr hc.le)
  let e : EReal ≃o EReal :=
    { toFun := fun x => (c : EReal) * x
      invFun := fun x => ((c⁻¹ : ℝ) : EReal) * x
      left_inv := fun x => by simp only; rw [← mul_assoc, h2, one_mul]
      right_inv := fun x => by simp only; rw [← mul_assoc, h1, one_mul]
      map_rel_iff' := by
        intro a b
        simp only [Equiv.coe_fn_mk]
        constructor
        · intro h
          have := mul_le_mul_of_nonneg_left h hc1
          rwa [← mul_assoc, ← mul_assoc, h2, one_mul, one_mul] at this
        · intro h; exact mul_le_mul_of_nonneg_left h hc0 }
  let f : EReal ≃o EReal :=
    { toFun := fun x => x + (d : EReal)
      invFun := fun x => x - (d : EReal)
      left_inv := fun x => EReal.add_sub_cancel_right
      right_inv := fun x => EReal.sub_add_cancel
      map_rel_iff' := by
        intro a b
        exact (EReal.addLECancellable_coe d).add_le_add_iff_right }
  e.trans f

lemma h54d_aff_apply (c d : ℝ) (hc : 0 < c) (x : EReal) :
    h54d_aff c d hc x = (c : EReal) * x + (d : EReal) := rfl

lemma h54d_cross {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    crossEntropy rho sigma =
      (Real.log 2 : EReal) * relativeEntropy rho sigma + ((Real.log 2 * vnEntropy rho : ℝ) : EReal) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcfc : cfc (fun x : ℝ => x * Real.logb 2 x) rho =
      ((Real.log 2)⁻¹ : ℝ) • cfc (fun x : ℝ => x * Real.log x) rho := by
    rw [← cfc_smul (R := ℝ) ((Real.log 2)⁻¹) (fun x : ℝ => x * Real.log x) rho
      (Real.continuous_mul_log.continuousOn)]
    congr 1
    funext x; simp only [smul_eq_mul, Real.logb]; ring
  have hfin : crossEntropyFinite rho sigma =
      Real.log 2 * relativeEntropyFinite rho sigma + Real.log 2 * vnEntropy rho := by
    unfold crossEntropyFinite relativeEntropyFinite vnEntropy
    rw [hcfc, Matrix.trace_smul, Complex.smul_re, Matrix.trace_sub, Complex.sub_re]
    simp only [smul_eq_mul]
    generalize (cfc (fun x : ℝ => x * Real.log x) rho).trace.re = a
    generalize (rho * cfc Real.log sigma).trace.re = b
    field_simp
    ring
  unfold crossEntropy relativeEntropy
  split_ifs
  · rw [hfin, ← EReal.coe_mul, ← EReal.coe_add]
  · have : (0 : EReal) < (Real.log 2 : EReal) := by exact_mod_cast hl
    rw [EReal.mul_top_of_pos this, EReal.top_add_coe]

theorem solution {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    crossEntropyOptimum rho = (Real.log 2 : EReal) * rains rho +
      (Real.log 2 * vnEntropy rho : EReal) ∧
    (∀ sigma : Matrix (A × B) (A × B) ℂ, pptPrime sigma →
      (relativeEntropy rho sigma = rains rho ↔
        crossEntropy rho sigma = crossEntropyOptimum rho)) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let e := h54d_aff (Real.log 2) (Real.log 2 * vnEntropy rho) hl
  have hcast : ((Real.log 2 * vnEntropy rho : ℝ) : EReal) = (Real.log 2 * vnEntropy rho : EReal) := by
    push_cast; rfl
  have hopt : crossEntropyOptimum rho = e (rains rho) := by
    unfold crossEntropyOptimum rains
    rw [OrderIso.map_sInf, ← sInf_image]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨sigma, hs, rfl⟩
      refine ⟨_, ⟨sigma, hs, rfl⟩, ?_⟩
      rw [h54d_cross]; rfl
    · rintro ⟨y, ⟨sigma, hs, rfl⟩, rfl⟩
      exact ⟨sigma, hs, by rw [h54d_cross]; rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hopt, h54d_aff_apply, hcast]
  · intro sigma _
    rw [hopt, h54d_cross]
    exact ⟨fun h => by rw [h]; rfl, fun h => e.injective h⟩

end
