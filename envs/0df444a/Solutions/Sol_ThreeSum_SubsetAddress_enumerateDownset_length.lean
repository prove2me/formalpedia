-- Prove2me | solution 1 for ThreeSum.SubsetAddress.enumerateDownset_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:36.243093+00:00
-- url     : https://prove2.me/submissions/b8a1133b-d8b6-4f62-ba64-241c39eee53e

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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateThrough_length

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution (L cut : ℕ) :
    (enumerateDownset L cut).length = downsetCap L cut :=
  enumerateThrough_length L (min cut L)
end ThreeSum.SubsetAddress
