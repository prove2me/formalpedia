-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linProj_smul_left_0afd722762be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:30.03173+00:00
-- url     : https://prove2.me/submissions/0902160b-45ae-4b41-9443-f1ae1db7dee4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment

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
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    linProj π (c • y) = c • linProj π y :=
  (linProjₗ π).map_smul c y
end GroundTheory.Heights₂.Heights
