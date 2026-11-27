-- Prove2me | solution 1 for PI.SelfDualLoc.W.hform_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:18:56.790627+00:00
-- url     : https://prove2.me/submissions/59b813fa-0266-4629-a854-fdc5d42a6470

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Theorems.Thm_PI_SelfDualLoc_W_hform_add_right
import Theorems.Thm_PI_SelfDualLoc_W_hform_zero_right

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
theorem _root_.solution {ι : Type} (s : Finset ι) (x : n → A) (f : ι → n → A) :
    hform σ J x (∑ k ∈ s, f k) = ∑ k ∈ s, hform σ J x (f k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact hform_zero_right σ J x
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_right, ih]
end PI.SelfDualLoc.W
