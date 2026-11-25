-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_FlagRootProduct_rootPairing_eq_abs_9602f3ef690b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:37:17.172191+00:00
-- url     : https://prove2.me/submissions/8eda2634-f275-4d88-bd0d-f4eb87905c15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagRootProduct
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
namespace GroundTheory.Heights₂.Heights.FourB
namespace FlagRootProduct
theorem _root_.solution {N p : ℕ} {lam : Fin N → ℝ}
    (hd : IsSplitDominant N p lam) (q : LowerPair N) :
    rootPairing N p lam q = |lam q.1.1 - lam q.1.2| := by
  obtain ⟨⟨a, b⟩, hba⟩ := q
  have hba' : b.val < a.val := hba
  have ha := a.isLt
  have hb := b.isLt
  unfold rootPairing
  dsimp only
  by_cases h : b.val < p ∧ p ≤ a.val
  · rw [if_pos h]
    have hle : lam b ≤ lam a := hd a b (by
      unfold splitRank
      rw [if_pos h.2, if_neg (by omega)]
      omega)
    rw [abs_of_nonneg (by linarith)]
  · rw [if_neg h]
    have hle : lam a ≤ lam b := hd b a (by
      unfold splitRank
      split_ifs <;> omega)
    rw [abs_of_nonpos (by linarith)]
    ring
end FlagRootProduct
end GroundTheory.Heights₂.Heights.FourB
