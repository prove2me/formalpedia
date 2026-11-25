-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DefectAverage_hypotheses_inhabited_f83caa6d54fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:58:03.757054+00:00
-- url     : https://prove2.me/submissions/08a97bfb-2fe6-433e-95e2-42f6e57e2565

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_data_824ef48ddc21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_point_admissible_38b0f2f4122d

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
namespace DefectAverage
theorem _root_.solution :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) 0 1 (X (0, 0)) ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) (fun _ => 1) :=
  ⟨MahlerInhabit.point_data, MahlerInhabit.point_admissible⟩
end DefectAverage
end GroundTheory.Heights₂.Heights
