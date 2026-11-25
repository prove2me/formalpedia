-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.h_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:01.451966+00:00
-- url     : https://prove2.me/submissions/329dfe03-89bb-4cde-b3fe-921dad3f3b9b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg

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
theorem _root_.solution (y : n → A) : Formalism.UG.hform σ J 0 y = 0 := by
  simp [Formalism.UG.hform]
end PI.UnitaryDimensionFormula.FrameAlg
