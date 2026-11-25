-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_sum_Ico_telescope_a33e672943b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:14.436674+00:00
-- url     : https://prove2.me/submissions/09809333-0d5b-405a-af30-d5fce3e5ca8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (Λ : ℕ → ℝ) (b m : ℕ) :
    ∑ k ∈ Finset.Ico b (b + m), (Λ k - Λ (k + 1)) = Λ b - Λ (b + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show b + (m + 1) = b + m + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
    ring
end GroundTheory.Heights₂.Heights.FourB
