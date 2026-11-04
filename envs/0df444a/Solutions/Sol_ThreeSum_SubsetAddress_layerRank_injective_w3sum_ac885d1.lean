-- Prove2me | solution 1 for ThreeSum.SubsetAddress.layerRank_injective_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:53.734982+00:00
-- url     : https://prove2.me/submissions/14a9daf6-216f-4397-afc5-18ad0df893f8

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
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Definitions.Def_WeightedCache3SUM_Alias_a5ea34939403d75f
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L k m n : ℕ} (hm : IsMask L k m) (hn : IsMask L k n)
    (he : layerRank L k m = layerRank L k n) : m = n := by
  induction L generalizing k m n with
  | zero =>
      have hm' := hm.1
      have hn' := hn.1
      simp only [pow_zero] at hm' hn'
      omega
  | succ L ih =>
      by_cases hc : m < 2 ^ L <;> by_cases hd : n < 2 ^ L
      · apply ih (hm.low hc) (hn.low hd)
        simpa only [layerRank, if_pos hc, if_pos hd] using he
      · have hb := layerRank_lt (hm.low hc)
        simp only [layerRank, if_pos hc, if_neg hd] at he
        omega
      · have hb := layerRank_lt (hn.low hd)
        simp only [layerRank, if_neg hc, if_pos hd] at he
        omega
      · have hr := (hm.high (Nat.le_of_not_gt hc)).2
        have hs := (hn.high (Nat.le_of_not_gt hd)).2
        have hrest : layerRank L (k - 1) (m - 2 ^ L) =
            layerRank L (k - 1) (n - 2 ^ L) := by
          simpa only [layerRank, if_neg hc, if_neg hd, Nat.add_left_cancel_iff] using he
        have hi := ih hr hs hrest
        omega
end ThreeSum.SubsetAddress
