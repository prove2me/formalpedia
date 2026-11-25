-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.complexHessian_sum_normSq_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:20.71514+00:00
-- url     : https://prove2.me/submissions/98515e94-afeb-48a9-af80-5fba4f8956be

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_fderiv_sum_normSq
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_sqForm_single
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_smul_single_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution (z : Fin D → ℂ) :
    hessC (fun w => ∑ i, Complex.normSq (w i)) z = 1 := by
  have h : (fun w => sqForm D w + (sqForm D).flip w) = ⇑(sqForm D + (sqForm D).flip) := by
    funext w; rfl
  ext i j
  simp only [hessC, fderiv_sum_normSq, h, ContinuousLinearMap.fderiv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, smul_single_one, sqForm_single]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, Complex.inner]
    norm_num
  · simp [Matrix.one_apply, hij, Ne.symm hij]
end ReciprocityTheory.AnForm.A.TraceConjugationCover
