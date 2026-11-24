-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isometry_zeroExt_b287ac62694e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:28:09.314149+00:00
-- url     : https://prove2.me/submissions/45cb3101-1508-4907-8bb8-cc560becf41f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_norm_zeroExt_611dca0a2c09

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m k : ℕ) : Isometry (zeroExt m k) :=
  AddMonoidHomClass.isometry_of_norm (zeroExt m k) (norm_zeroExt m k)
end GroundTheory.Heights₂.Heights
