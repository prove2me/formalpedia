-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FsLogAverage_hypotheses_inhabited_bd29e1850784
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:44.084377+00:00
-- url     : https://prove2.me/submissions/124c3d34-5ea9-475f-94db-ecadfb3cbe85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_euclid_ne_zero_e36561b6c92a

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace FsLogAverage
theorem _root_.solution :
    (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1)) ≠ 0 :=
  MahlerInhabit.euclid_ne_zero
end FsLogAverage
end GroundTheory.Heights₂.Heights
