-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.h_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:19.875711+00:00
-- url     : https://prove2.me/submissions/777875e8-dd63-422e-a984-1c5edd040d82

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_add_left
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI PI.UnitaryDimensionFormula PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
namespace PI.UnitaryDimensionFormula.FrameAlg
theorem _root_.solution {ι : Type} (s : Finset ι) (v : ι → n → A) (y : n → A) :
    Formalism.UG.hform σ J (∑ l ∈ s, v l) y = ∑ l ∈ s, Formalism.UG.hform σ J (v l) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_left, ih]
end PI.UnitaryDimensionFormula.FrameAlg
