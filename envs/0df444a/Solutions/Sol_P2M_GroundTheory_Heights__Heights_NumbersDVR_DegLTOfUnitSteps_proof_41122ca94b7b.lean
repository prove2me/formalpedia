-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTOfUnitSteps_proof_41122ca94b7b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:11.523934+00:00
-- url     : https://prove2.me/submissions/53459ebf-32d1-4766-8fe2-ec7cff99fb49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTOfUnitSteps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTOfUnitSteps_degLT_diffStep_f67a5cef2aae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DegLTOfUnitSteps
theorem _root_.solution (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement) :
    DegLTOfUnitSteps.Statement := by
  intro K _ _ n f hf bs
  have key : mixedDiff bs f = mixedDiff (Fin.tail bs) (diffStep (bs 0) f) := by
    rw [(h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.1,
      ← (h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.2]
    congr 1
    exact (Fin.cons_self_tail bs).symm
  rw [key]
  exact DegLTOfUnitSteps.degLT_diffStep h1 h2 h3 K n f hf (bs 0) _
end DegLTOfUnitSteps
end GroundTheory.Heights₂.Heights.NumbersDVR
