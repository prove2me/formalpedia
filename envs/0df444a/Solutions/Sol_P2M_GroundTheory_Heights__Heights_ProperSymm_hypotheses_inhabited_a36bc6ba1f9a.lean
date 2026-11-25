-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProperSymm_hypotheses_inhabited_a36bc6ba1f9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:50.451643+00:00
-- url     : https://prove2.me/submissions/e0c54647-c241-4e0c-bf78-68177a6af846

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_prime_pair_30334369fc3b

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
namespace ProperSymm
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (MahlerInhabit.coord 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (MahlerInhabit.coord 1) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      IsAdmissible (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (MahlerInhabit.coord 0)) (MahlerInhabit.coord 1) :=
  MahlerInhabit.line_prime_pair
end ProperSymm
end GroundTheory.Heights₂.Heights
