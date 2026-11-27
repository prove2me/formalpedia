-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SectionNef_equiv_77d18ef4e695
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:45.662484+00:00
-- url     : https://prove2.me/submissions/2857d8a0-498e-4cfd-9ed4-8363856a2580

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSectionNef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueBundlesSecondOfFirstAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SectionNef_glueBundles_second_of_first_2f3b8db046e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_GradedFinite_proof_4a0254b94345
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SectionNefGenerated_proof_bf5ccf2f9407
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SectionNef_proof_7ba5c90ed895
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ColonMultiHomog_proof_89514dc80a8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open GroundTheory.Heights₂.Heights.NumbersDVR
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace SectionNef
theorem _root_.solution :
    (_root_.GroundTheory.Heights₂.Heights.Model.SectionNef.Statement ∧
      _root_.GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.Statement) ↔
      SectionNef.Statement :=
  ⟨fun h => SectionNef.glueBundles_second_of_first h.1, fun _ =>
    ⟨_root_.GroundTheory.Heights₂.Heights.Model.SectionNef.proof,
      _root_.GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.proof⟩⟩
end SectionNef
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
