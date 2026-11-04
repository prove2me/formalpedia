-- Prove2me | solution 1 for ThreeSum.SubsetAddress.throughWork_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:56.866271+00:00
-- url     : https://prove2.me/submissions/0af39bb2-4a73-403f-b477-c72bc4bfd254

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
import Definitions.Def_WeightedCache3SUM_Alias_85ca0f35704fc2ef
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_succ
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateThrough_length
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L k : ℕ) :
    throughWork L k ≤ (4 * L + k + 1) * layerOffset L (k + 1) + 2 * k + 1 := by
  induction k with
  | zero => simp [throughWork, enumerationWork, layerOffset_succ]
  | succ k ih =>
      have hl := enumerationWork_bound L (k + 1)
      simp only [throughWork, enumerateThrough_length]
      rw [layerOffset_succ L (k + 1)]
      nlinarith
end ThreeSum.SubsetAddress
