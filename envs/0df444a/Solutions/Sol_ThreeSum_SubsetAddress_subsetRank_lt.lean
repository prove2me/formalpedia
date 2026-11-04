-- Prove2me | solution 1 for ThreeSum.SubsetAddress.subsetRank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:05.193195+00:00
-- url     : https://prove2.me/submissions/ea335cd6-d58e-47a0-93ae-1eea4bdcdc1b

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
import Theorems.Thm_ThreeSum_SubsetAddress_downsetRank_lt
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask

set_option autoImplicit false
open ThreeSum ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace ThreeSum.SubsetAddress
theorem _root_.solution {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    subsetRank s < downsetCap L cut := by
  have hm := subsetMask_isMask s
  exact downsetRank_lt hm.1 (hm.2.trans_le hs)
end ThreeSum.SubsetAddress
