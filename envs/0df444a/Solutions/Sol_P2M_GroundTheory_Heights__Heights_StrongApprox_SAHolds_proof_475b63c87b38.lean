-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_proof_475b63c87b38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:45.759015+00:00
-- url     : https://prove2.me/submissions/30794b6b-f095-41d6-b227-3434f3e47f49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PSAHolds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_of_neighbourhoods_truncation_7c2c028ab7e1

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
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace SAHolds
theorem _root_.solution (_hHyp : HypPairExists.Statement) (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement :=
  SAHolds.of_neighbourhoods_truncation hNb hTr
end SAHolds
end GroundTheory.Heights₂.Heights.StrongApprox
