-- Prove2me | solution 1 for ThreeSum.SparseBoxes.no_queryBox_of_few_missing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:34.942352+00:00
-- url     : https://prove2.me/submissions/5d3bbcfe-9015-48d8-a918-1c23d12d6634

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Theorems.Thm_ThreeSum_SparseBoxes_queryBox_iff_separator

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q leaf u : Finset α) (t : ℕ)
    (hu : u ∈ q.powersetCard t) (hsmall : (q \ leaf).card < t) :
    ¬ QueryBox q u leaf := by
  intro hb
  obtain ⟨huq, huc⟩ := Finset.mem_powersetCard.mp hu
  have hsub := ((queryBox_iff_separator q u leaf huq).mp hb).2.1
  have hc := Finset.card_le_card hsub
  omega
end ThreeSum.SparseBoxes
