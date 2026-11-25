-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:50.311935+00:00
-- url     : https://prove2.me/submissions/7375d6b2-e078-438b-85c2-ec08054713d5

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
section Lv
variable {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
private theorem smul_decomp (c : ℂ) (a : Fin D → ℂ) :
    c • a = c.re • a + c.im • (I • a) ∧ I • (c • a) = c.re • (I • a) - c.im • a := by
  constructor
  · ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  · ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination ((c.im : ℂ) * a k) * Complex.I_sq
end Lv
section Comp
variable {D E : ℕ}
end Comp
section SqForm
variable {D : ℕ}
end SqForm
end
end ReciprocityTheory.AnForm.A.TraceConjugationCover
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
variable {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution (c : ℂ) (a b : Fin D → ℂ) : lv H (c • a) b = c * lv H a b := by
  obtain ⟨h1, h2⟩ := smul_decomp c a
  unfold lv
  rw [h2, h1]
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring
end ReciprocityTheory.AnForm.A.TraceConjugationCover
