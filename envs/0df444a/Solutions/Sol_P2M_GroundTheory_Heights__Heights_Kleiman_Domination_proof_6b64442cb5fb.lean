-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_proof_6b64442cb5fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:34:54.122237+00:00
-- url     : https://prove2.me/submissions/b3b55b29-872b-43fe-b9aa-a5608a896b72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_Generic_proof_f0afc2d97b29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_Normal_proof_52035cac6f86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_Conductor_proof_360c8994b5ee

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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution (hF : FiniteSections.Statement.{w, w}) : Domination.Statement.{u, w} :=
  ⟨Generic.proof hF, Normal.proof hF, Conductor.proof hF⟩
end GroundTheory.Heights₂.Heights.Kleiman.Domination
