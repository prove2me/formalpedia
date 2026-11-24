-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.pgtlCx_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:57.968843+00:00
-- url     : https://prove2.me/submissions/af802fdf-b2c9-4acf-8cad-c3effb21abf9

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
theorem _root_.solution (d : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) : (pgtlCx d z).re = d z := by
  simp [pgtlCx_apply]
end ReciprocityTheory.GeometryOfNumbersTheory
