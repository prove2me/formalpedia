-- Prove2me | solution 1 for ThreeSum.SubsetAddress.recordAddress_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:20.034928+00:00
-- url     : https://prove2.me/submissions/8255aa14-2015-43cd-80c8-e228621bc201

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
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_injective
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L : ℕ} {s t : Finset (Fin L)} {e f : ℕ}
    (he : e ≤ L) (hf : f ≤ L) (h : recordAddress s e = recordAddress t f) :
    s = t ∧ e = f := by
  have he' : e < L + 1 := by omega
  have hf' : f < L + 1 := by omega
  have hfree : e = f := by
    have hmod := congrArg (fun x => x % (L + 1)) h
    simpa [recordAddress, Nat.add_mod, Nat.mod_eq_of_lt he', Nat.mod_eq_of_lt hf'] using hmod
  have hmul : subsetRank s * (L + 1) = subsetRank t * (L + 1) := by
    unfold recordAddress at h
    omega
  have hr : subsetRank s = subsetRank t := Nat.eq_of_mul_eq_mul_right (by omega) hmul
  exact ⟨subsetRank_injective L hr, hfree⟩
end ThreeSum.SubsetAddress
