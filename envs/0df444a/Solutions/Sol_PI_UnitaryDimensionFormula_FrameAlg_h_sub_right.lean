-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.h_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:16.878598+00:00
-- url     : https://prove2.me/submissions/e29499ee-6cb7-41e2-af3a-fbddd596a97d

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
theorem _root_.solution (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end PI.UnitaryDimensionFormula.FrameAlg
