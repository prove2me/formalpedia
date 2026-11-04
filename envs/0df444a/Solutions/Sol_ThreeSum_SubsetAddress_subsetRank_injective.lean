-- Prove2me | solution 1 for ThreeSum.SubsetAddress.subsetRank_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:58.848753+00:00
-- url     : https://prove2.me/submissions/3a4e92c3-8826-4666-91d7-85c45c0b3c31

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
import Theorems.Thm_ThreeSum_SubsetAddress_downsetRank_injective
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_injective

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L : ℕ) : Function.Injective (@subsetRank L) := by
  intro s t he
  apply subsetMask_injective L
  exact downsetRank_injective (subsetMask_isMask s).1 (subsetMask_isMask t).1 he
end ThreeSum.SubsetAddress
