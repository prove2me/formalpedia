-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_MertensUpper_Iic_eq_range_ccd3cc9ac0de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:51.233052+00:00
-- url     : https://prove2.me/submissions/e34c5165-8ddd-40e7-bdf0-0b38c6e5653f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IicEqRange

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
theorem _root_.solution (n : ℕ) : Finset.Iic n = Finset.range (n + 1) := by
  ext m
  simp
end MertensUpper
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
