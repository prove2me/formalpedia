-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.fB_eq_TB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:35.040027+00:00
-- url     : https://prove2.me/submissions/afea06db-bba3-4e31-a98b-3c815a65aab4

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) : fB B x = TB B (fB 1 x) := by
  simp [fB_apply, TB, Matrix.one_mulVec]
end ReciprocityTheory.ReducedBases.T2
