-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.h_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:55.721603+00:00
-- url     : https://prove2.me/submissions/7715dbe9-3cc7-4099-bac7-17425ac0e91c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_add_right
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_zero_right

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
theorem _root_.solution {ι : Type} (s : Finset ι) (x : n → A) (v : ι → n → A) :
    Formalism.UG.hform σ J x (∑ l ∈ s, v l) = ∑ l ∈ s, Formalism.UG.hform σ J x (v l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_right, ih]
end PI.UnitaryDimensionFormula.FrameAlg
