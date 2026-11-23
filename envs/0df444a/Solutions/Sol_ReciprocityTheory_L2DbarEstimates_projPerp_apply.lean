-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.projPerp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:46.777806+00:00
-- url     : https://prove2.me/submissions/a3eaab45-880d-41e6-a5f6-2664aa47fefd

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (g : Fin p → ℂ) (i l : Fin p) :
    projPerp g i l = (if i = l then 1 else 0) - ((sqNorm g : ℝ) : ℂ)⁻¹ * (g i * conj (g l)) := by
  simp [projPerp, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, Complex.star_def]
end ReciprocityTheory.L2DbarEstimates
