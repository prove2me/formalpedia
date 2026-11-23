-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.fB_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:59.79048+00:00
-- url     : https://prove2.me/submissions/12e48b86-ce5a-40cd-bcad-ed073eb4d233

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective

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
theorem _root_.solution (B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) :
    fB B x = WithLp.toLp 2 (B *ᵥ toReal x) := rfl
end ReciprocityTheory.ReducedBases.T2
