-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_linEval_single_last_358238134de1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:27.927059+00:00
-- url     : https://prove2.me/submissions/9ad3d785-ccb5-477a-919b-2eacbb5c7b49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongPolyLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StVarIntGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLocalMultComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongPolyLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {n : ℕ} (x : Fin (n + 1) → ℂ) :
    linEval (Pi.single (Fin.last n) 1) x = x (Fin.last n) := by
  simp [linEval, Pi.single_apply]
end GroundTheory.Heights₂.Heights.Targets
