-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.pgtlBil_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:17.595357+00:00
-- url     : https://prove2.me/submissions/55cc9414-fb2e-4185-8a6e-89f34e172dea

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt

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
theorem _root_.solution (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z w : Fin D → ℂ) :
    pgtlBil B z w = pgtlCx (pgtlDz B z) w := rfl
end ReciprocityTheory.GeometryOfNumbersTheory
