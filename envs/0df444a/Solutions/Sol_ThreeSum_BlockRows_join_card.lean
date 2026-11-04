-- Prove2me | solution 1 for ThreeSum.BlockRows.join_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:30.034201+00:00
-- url     : https://prove2.me/submissions/9e52248d-eb5c-4623-959a-6ee689814dd8

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_BlockRows

set_option autoImplicit false
open ThreeSum ThreeSum.BlockRows
open Finset
open scoped BigOperators
namespace ThreeSum.BlockRows
theorem _root_.solution {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _
end ThreeSum.BlockRows
