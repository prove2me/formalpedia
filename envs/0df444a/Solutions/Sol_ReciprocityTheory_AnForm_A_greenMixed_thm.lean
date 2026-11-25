-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.greenMixed_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:49.735131+00:00
-- url     : https://prove2.me/submissions/5f079419-7b77-414f-9daa-b5f1006151e3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Theorems.Thm_ReciprocityTheory_AnForm_A_log_coord_mul_hess

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : GreenMixedStatement := by
  intro D j a b u hu hs hab
  have hcase : ((Pi.single a 1 : Fin (D + 1) → ℂ) j = 0 ∧
        (Complex.I • (Pi.single a 1 : Fin (D + 1) → ℂ)) j = 0) ∨
      ((Pi.single b 1 : Fin (D + 1) → ℂ) j = 0 ∧
        (Complex.I • (Pi.single b 1 : Fin (D + 1) → ℂ)) j = 0) := by
    by_cases ha : j = a
    · subst ha
      have hb : j ≠ b := fun h => hab (by rw [← h])
      right; simp [Pi.single_eq_of_ne hb]
    · left; simp [Pi.single_eq_of_ne ha]
  have hvw : ∀ v w : Fin (D + 1) → ℂ,
      (v = Pi.single a 1 ∨ v = Complex.I • Pi.single a 1) →
      (w = Pi.single b 1 ∨ w = Complex.I • Pi.single b 1) → v j = 0 ∨ w j = 0 := by
    rintro v w (rfl | rfl) (rfl | rfl) <;> tauto
  obtain ⟨i1, e1⟩ := log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inl rfl) (Or.inl rfl))
  obtain ⟨i2, e2⟩ := log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inr rfl) (Or.inr rfl))
  obtain ⟨i3, e3⟩ := log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inl rfl) (Or.inr rfl))
  obtain ⟨i4, e4⟩ := log_coord_mul_hess j hu hs _ _ (hvw _ _ (Or.inr rfl) (Or.inl rfl))
  have hfun : (fun z : Fin (D + 1) → ℂ =>
      (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b) = fun z =>
      (((Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Pi.single a 1) (Pi.single b 1) +
        Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Complex.I • Pi.single a 1)
          (Complex.I • Pi.single b 1)) / 4 : ℝ) : ℂ) +
      Complex.I * (((Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Pi.single a 1)
          (Complex.I • Pi.single b 1) -
        Real.log ‖z j‖ * fderiv ℝ (fderiv ℝ u) z (Complex.I • Pi.single a 1)
          (Pi.single b 1)) / 4 : ℝ) : ℂ) := by
    funext z
    simp only [ReciprocityTheory.AnForm.hessC]
    push_cast
    ring
  rw [hfun]
  refine ⟨((i1.add i2).div_const 4).ofReal.add (((i3.sub i4).div_const 4).ofReal.const_mul _), ?_⟩
  rw [integral_add ((i1.add i2).div_const 4).ofReal
      (((i3.sub i4).div_const 4).ofReal.const_mul _), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, integral_div, integral_div, integral_add i1 i2, integral_sub i3 i4, e1, e2,
    e3, e4]
  simp
end ReciprocityTheory.AnForm.A
