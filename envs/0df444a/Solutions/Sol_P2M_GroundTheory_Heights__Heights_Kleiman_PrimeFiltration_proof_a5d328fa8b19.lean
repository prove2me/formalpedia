-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_proof_a5d328fa8b19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:37:42.764635+00:00
-- url     : https://prove2.me/submissions/eaffc1c9-e5ef-4fb5-80ea-795698d45939

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Irrelevant_proof_a0f9d6421b8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Point_proof_d22f31b4a055
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Restrict_proof_9254d696b6ca


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace PrimeFiltration
theorem _root_.solution (hE : PrimeFiltration.Exists.Statement.{u, v, w}) :
    PrimeFiltration.Statement.{u, v, w} :=
  ⟨hE, PrimeFiltration.Irrelevant.proof, PrimeFiltration.Point.proof,
    PrimeFiltration.Restrict.proof⟩
end PrimeFiltration
end GroundTheory.Heights₂.Heights.Kleiman
