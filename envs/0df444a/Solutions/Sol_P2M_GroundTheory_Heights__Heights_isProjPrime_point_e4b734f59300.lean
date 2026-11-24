-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:23.740817+00:00
-- url     : https://prove2.me/submissions/cc35fca9-ede8-4137-bad9-a53979639291

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (F : Type*) [Field F] :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) F)) where
  isPrime := Ideal.isPrime_bot
  isHomog f hf d := by
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  isRelevant := ⟨0, by rw [Ideal.mem_bot]; exact X_ne_zero 0⟩
end GroundTheory.Heights₂.Heights
