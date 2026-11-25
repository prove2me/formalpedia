-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_proof_a0b2351b3136
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:33.164613+00:00
-- url     : https://prove2.me/submissions/9535d91a-fdb0-4d39-8432-d8c042da8b4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_of_placeMaps_c4be2c416734

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
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
theorem _root_.solution (_hT : AETopologicalRing.Statement) (hP : PlaceMaps.Statement) :
    AENeighbourhoods.Statement :=
  of_placeMaps hP
end GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
