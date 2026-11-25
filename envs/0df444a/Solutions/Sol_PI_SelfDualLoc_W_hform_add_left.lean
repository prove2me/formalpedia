-- Prove2me | solution 1 for PI.SelfDualLoc.W.hform_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:16.207553+00:00
-- url     : https://prove2.me/submissions/e491d47b-b569-4636-a8de-2298e2d7472e

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
theorem _root_.solution (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [PI.SelfDualLoc.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
end PI.SelfDualLoc.W
