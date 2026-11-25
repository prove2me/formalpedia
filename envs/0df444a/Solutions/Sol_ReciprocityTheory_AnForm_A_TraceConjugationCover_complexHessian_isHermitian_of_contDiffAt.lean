-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.complexHessian_isHermitian_of_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:58.312733+00:00
-- url     : https://prove2.me/submissions/6af07fc4-1858-476e-9dd2-c624a9252926

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_hessC_eq_lv

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
variable {D E : ℕ}
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  have hs : IsSymmSndFDerivAt ℝ φ z := hφ.isSymmSndFDerivAt (by simp)
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [hessC_eq_lv, lv]
  rw [hs (Pi.single j 1) (Pi.single i 1), hs (I • Pi.single j 1) (I • Pi.single i 1),
    hs (Pi.single j 1) (I • Pi.single i 1), hs (I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp
end ReciprocityTheory.AnForm.A.TraceConjugationCover
