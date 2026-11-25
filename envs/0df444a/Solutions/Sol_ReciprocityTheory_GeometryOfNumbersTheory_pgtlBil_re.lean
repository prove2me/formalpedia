-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.pgtlBil_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:16.122706+00:00
-- url     : https://prove2.me/submissions/a16a4959-e173-42f7-91ef-87d3beb49b55

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtlCx_re
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtlBil_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Complex
variable {D : ℕ}
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (pgtlBil B z z).re = (B z z - B (I • z) (I • z)) / 4 := by
  rw [pgtlBil_apply, pgtlCx_re, pgtlDz_apply]
end ReciprocityTheory.GeometryOfNumbersTheory
