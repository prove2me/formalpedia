-- Prove2me | solution 1 for PI.SelfDualLoc.W.hform_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:22.905144+00:00
-- url     : https://prove2.me/submissions/2e007c48-af28-4753-b5a7-145ca1753557

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (σ : A →+* A) (J : Matrix n n A)
namespace PI.SelfDualLoc.W
theorem _root_.solution (y : n → A) : hform σ J 0 y = 0 := by
  simp [PI.SelfDualLoc.hform]
end PI.SelfDualLoc.W
