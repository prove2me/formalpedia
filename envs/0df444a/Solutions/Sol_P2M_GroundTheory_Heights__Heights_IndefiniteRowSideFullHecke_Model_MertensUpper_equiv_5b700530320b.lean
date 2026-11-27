-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_MertensUpper_equiv_5b700530320b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:05:06.986592+00:00
-- url     : https://prove2.me/submissions/d5b4dc19-0cf4-470f-abfc-844a2b640535

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IicEqRange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_MertensUpper_Iic_eq_range_ccd3cc9ac0de

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace MertensUpper
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement := by
  unfold GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement
  simp only [MertensUpper.Iic_eq_range]
end MertensUpper
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
