-- Prove2me | solution 1 for ThreeSum.SubsetAddress.IsMask.low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:14.573248+00:00
-- url     : https://prove2.me/submissions/61752110-66d1-4dbe-9140-665834538b51

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
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
namespace IsMask
theorem _root_.solution {L k m : ℕ} (hm : IsMask (L + 1) k m) (hc : m < 2 ^ L) :
    IsMask L k m := ⟨hc, by simpa [weight, hc] using hm.2⟩
end IsMask
end ThreeSum.SubsetAddress
