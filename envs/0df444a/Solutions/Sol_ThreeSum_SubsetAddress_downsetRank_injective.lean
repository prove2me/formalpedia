-- Prove2me | solution 1 for ThreeSum.SubsetAddress.downsetRank_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:15.890722+00:00
-- url     : https://prove2.me/submissions/f543ca20-95f2-41ee-832c-88ed6ff00084

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
import Definitions.Def_WeightedCache3SUM_Alias_a5ea34939403d75f
import Definitions.Def_WeightedCache3SUM_Alias_12666df80ddc7204
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_succ
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_mono
namespace ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
private theorem downsetRank_lt_of_weight_lt {L m n : ℕ} (hm : m < 2 ^ L)
    (hk : weight L m < weight L n) : downsetRank L m < downsetRank L n := by
  have hr := layerRank_lt (show IsMask L (weight L m) m from ⟨hm, rfl⟩)
  have ho := layerOffset_mono L hk
  rw [layerOffset_succ] at ho
  unfold downsetRank
  omega
end ThreeSum.SubsetAddress
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L m n : ℕ} (hm : m < 2 ^ L) (hn : n < 2 ^ L)
    (he : downsetRank L m = downsetRank L n) : m = n := by
  rcases lt_trichotomy (weight L m) (weight L n) with hk | hk | hk
  · have hlt := downsetRank_lt_of_weight_lt hm hk
    omega
  · have hr : layerRank L (weight L m) m = layerRank L (weight L m) n := by
      unfold downsetRank at he
      rw [← hk] at he
      omega
    exact layerRank_injective ⟨hm, rfl⟩ ⟨hn, hk.symm⟩ hr
  · have hlt := downsetRank_lt_of_weight_lt hn hk
    omega
end ThreeSum.SubsetAddress
