-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_sum_fin_telescope_d731859c771b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:07.554738+00:00
-- url     : https://prove2.me/submissions/ab1e57ed-967a-4da0-bbc9-96ebb5d8a3ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sum_Ico_telescope_a33e672943b8
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
theorem _root_.solution {N : ℕ} (Λ : ℕ → ℝ) (b c : ℕ) (hbc : b < c) (hc : c ≤ N) :
    ∑ k : Fin N, (if b ≤ k.val ∧ k.val < c then Λ k - Λ (k.val + 1) else 0) = Λ b - Λ c := by
  rw [show (∑ k : Fin N, (if b ≤ k.val ∧ k.val < c then Λ k - Λ (k.val + 1) else 0)) =
      ∑ k ∈ Finset.range N, (if b ≤ k ∧ k < c then Λ k - Λ (k + 1) else 0) from
    Fin.sum_univ_eq_sum_range (fun k => if b ≤ k ∧ k < c then Λ k - Λ (k + 1) else 0) N]
  rw [← Finset.sum_filter]
  have : (Finset.range N).filter (fun k => b ≤ k ∧ k < c) = Finset.Ico b (b + (c - b)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, sum_Ico_telescope, Nat.add_sub_cancel' hbc.le]
end GroundTheory.Heights₂.Heights.FourB
