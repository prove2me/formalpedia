-- Prove2me | solution 1 for ThreeSum.SubsetAddress.subsetMask_mem_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:12:59.634708+00:00
-- url     : https://prove2.me/submissions/f23e1468-d668-453b-bb9b-2effc44b0f58

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
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateDownset
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetMask s ∈ enumerateDownset L cut := by
  apply (mem_enumerateDownset L cut _).mpr
  have hm := subsetMask_isMask s
  exact ⟨hm.1, hm.2.trans_le hs⟩
end ThreeSum.SubsetAddress
