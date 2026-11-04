-- Prove2me | solution 1 for ThreeSum.SubsetAddress.downsetRank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:54.797502+00:00
-- url     : https://prove2.me/submissions/2c0a6e05-cf60-41bb-9e2a-0a286a15bcab

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
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_le_width
import Definitions.Def_WeightedCache3SUM_Alias_a5ea34939403d75f
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_succ
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_mono

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L cut m : ℕ} (hm : m < 2 ^ L) (hk : weight L m ≤ cut) :
    downsetRank L m < downsetCap L cut := by
  have hmask : IsMask L (weight L m) m := ⟨hm, rfl⟩
  have hr := layerRank_lt hmask
  unfold downsetRank downsetCap
  calc
    _ < layerOffset L (weight L m) + L.choose (weight L m) := Nat.add_lt_add_left hr _
    _ = layerOffset L (weight L m + 1) := (layerOffset_succ L _).symm
    _ ≤ _ := layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))
end ThreeSum.SubsetAddress
