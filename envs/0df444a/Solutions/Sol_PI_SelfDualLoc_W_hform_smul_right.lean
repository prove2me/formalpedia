-- Prove2me | solution 1 for PI.SelfDualLoc.W.hform_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:23.71099+00:00
-- url     : https://prove2.me/submissions/295a8690-7628-413b-886a-990c836dedb3

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
theorem _root_.solution (x : n → A) (c : A) (y : n → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [PI.SelfDualLoc.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PI.SelfDualLoc.W
