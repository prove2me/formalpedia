-- Prove2me | solution 1 for ThreeSum.SubsetAddress.subsetMask_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:22.210186+00:00
-- url     : https://prove2.me/submissions/e43cf1a9-1427-4736-95d3-2dfac1d7690b

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
import Theorems.Thm_ThreeSum_SubsetAddress_maskOf_injective
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_injective

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L : ℕ) : Function.Injective (@subsetMask L) :=
  maskOf_injective.comp (natPositions_injective L)
end ThreeSum.SubsetAddress
