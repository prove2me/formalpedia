-- Prove2me | solution 1 for PI.SelfDualLoc.W.hform_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:21.209815+00:00
-- url     : https://prove2.me/submissions/71db33f7-65df-4f46-9444-23b2e68e7046

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Theorems.Thm_PI_SelfDualLoc_W_hform_add_left
import Theorems.Thm_PI_SelfDualLoc_W_hform_zero_left

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → n → A) (y : n → A) :
    hform σ J (∑ k ∈ s, f k) y = ∑ k ∈ s, hform σ J (f k) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hform_zero_left σ J y
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_left, ih]
end PI.SelfDualLoc.W
