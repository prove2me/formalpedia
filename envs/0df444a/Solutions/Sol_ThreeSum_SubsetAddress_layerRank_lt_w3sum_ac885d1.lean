-- Prove2me | solution 1 for ThreeSum.SubsetAddress.layerRank_lt_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:25.720213+00:00
-- url     : https://prove2.me/submissions/a6b6cc34-6507-4d41-ae8a-c46812abe9c9

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_le_width
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L k m : ℕ} (hm : IsMask L k m) : layerRank L k m < L.choose k := by
  induction L generalizing k m with
  | zero =>
      have hk := hm.le_width
      have : k = 0 := by omega
      simp [this, layerRank]
  | succ L ih =>
      by_cases hc : m < 2 ^ L
      · simpa only [layerRank, if_pos hc] using
          (ih (hm.low hc)).trans_le (Nat.choose_le_succ L k)
      · obtain ⟨hk, hr⟩ := hm.high (Nat.le_of_not_gt hc)
        have hb := ih hr
        rw [layerRank, if_neg hc, Nat.choose_succ_left L k hk]
        omega
end ThreeSum.SubsetAddress
