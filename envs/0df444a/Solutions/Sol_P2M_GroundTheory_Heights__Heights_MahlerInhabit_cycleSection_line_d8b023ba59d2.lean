-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerInhabit_cycleSection_line_d8b023ba59d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:12.23655+00:00
-- url     : https://prove2.me/submissions/b77db5c4-335d-4c8a-b138-177de952cf17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler

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
open GroundTheory.Heights₂.Heights.MahlerInhabit
namespace GroundTheory.Heights₂.Heights.MahlerInhabit
theorem _root_.solution (u : Fin 2 → ℂ) :
    cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) u = divCycle ⊥ u := by
  simp [cycleSection]
end GroundTheory.Heights₂.Heights.MahlerInhabit
