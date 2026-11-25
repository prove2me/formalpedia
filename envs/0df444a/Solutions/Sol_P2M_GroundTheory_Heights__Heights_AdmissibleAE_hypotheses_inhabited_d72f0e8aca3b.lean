-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AdmissibleAE_hypotheses_inhabited_d72f0e8aca3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:58:59.959802+00:00
-- url     : https://prove2.me/submissions/a9d322bf-a1c6-4fbe-a499-28ab550daf66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_relevant_8a932349755c

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
namespace AdmissibleAE
theorem _root_.solution :
    ∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support, IsRelevant W :=
  MahlerInhabit.point_relevant
end AdmissibleAE
end GroundTheory.Heights₂.Heights
