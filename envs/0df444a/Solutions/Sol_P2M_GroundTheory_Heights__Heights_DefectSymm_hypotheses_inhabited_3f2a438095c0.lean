-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DefectSymm_hypotheses_inhabited_3f2a438095c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:35.694155+00:00
-- url     : https://prove2.me/submissions/852a498e-1fc8-45c9-8a4e-a050ce22a2d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_pair_448a64dfacca

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
namespace DefectSymm
theorem _root_.solution :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 1 1 LineChowForm.D2 ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (MahlerInhabit.coord 0) ∧ IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (MahlerInhabit.coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (MahlerInhabit.coord 0)) (MahlerInhabit.coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (MahlerInhabit.coord 1)) (MahlerInhabit.coord 0) :=
  MahlerInhabit.line_pair
end DefectSymm
end GroundTheory.Heights₂.Heights
