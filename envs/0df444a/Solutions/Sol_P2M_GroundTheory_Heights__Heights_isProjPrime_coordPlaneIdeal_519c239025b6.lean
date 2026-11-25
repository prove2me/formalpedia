-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isProjPrime_coordPlaneIdeal_519c239025b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:32.457695+00:00
-- url     : https://prove2.me/submissions/6ae402cd-8b2a-41ac-b32a-c950789fd038

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_homogeneousComponent_aeval_coordPlaneSubst_6be6f2ef863d

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
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (hm : 0 < m) (k : ℕ) :
    IsProjPrime (coordPlaneIdeal m k) where
  isPrime := RingHom.ker_isPrime _
  isHomog f hf d := by
    rw [coordPlaneIdeal, RingHom.mem_ker] at hf ⊢
    rw [← homogeneousComponent_aeval_coordPlaneSubst, hf, map_zero]
  isRelevant := ⟨Fin.castAdd k ⟨0, hm⟩, by
    rw [coordPlaneIdeal, RingHom.mem_ker, aeval_X, coordPlaneSubst, Fin.append_left]
    exact X_ne_zero _⟩
end GroundTheory.Heights₂.Heights
