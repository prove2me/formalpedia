-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_blkEquiv_apply_b5c60a5abd6f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.841745+00:00
-- url     : https://prove2.me/submissions/622d9463-a830-441c-beed-a6bdd4ceca92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
theorem _root_.solution (i : Fin n) : blkEquiv n ⟨(), i⟩ = i := rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
