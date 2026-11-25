-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.h_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:06.675726+00:00
-- url     : https://prove2.me/submissions/6a2e2eb4-a5a0-40a1-ba1b-9f41f18afd92

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
theorem _root_.solution (x : n → A) : Formalism.UG.hform σ J x 0 = 0 := by
  simp [Formalism.UG.hform]
end PI.UnitaryDimensionFormula.FrameAlg
