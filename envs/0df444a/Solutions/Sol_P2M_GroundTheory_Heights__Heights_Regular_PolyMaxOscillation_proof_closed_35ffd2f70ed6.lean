-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PolyMaxOscillation_proof_closed_35ffd2f70ed6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:51.580704+00:00
-- url     : https://prove2.me/submissions/80e0820a-1fe1-48ef-99b8-6c21ca4649e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMaxOscillation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxOscillation_proof_a78a3cff7a91
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMaxLogConvex_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace PolyMaxOscillation
theorem _root_.solution : PolyMaxOscillation.Statement :=
  PolyMaxOscillation.proof ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm
end PolyMaxOscillation
end GroundTheory.Heights₂.Heights.Regular
