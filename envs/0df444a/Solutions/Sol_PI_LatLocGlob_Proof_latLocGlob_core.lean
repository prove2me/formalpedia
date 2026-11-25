-- Prove2me | solution 1 for PI.LatLocGlob.Proof.latLocGlob_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:48.253617+00:00
-- url     : https://prove2.me/submissions/d8c0f8f5-9ecb-4320-8b53-00c3806be380

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
import Theorems.Thm_PI_LatLocGlob_Proof_exists_unique_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
namespace PI.LatLocGlob.Proof
theorem _root_.solution : LatLocGlob := by
  intro R K V _ _ _ _ _ _ _ _ _ _ L0 hL0 M hM hfin
  exact exists_unique_lat L0 hL0 M hM hfin
end PI.LatLocGlob.Proof
