-- Prove2me | solution 1 for ThreeSum.BlockRows.forced_sizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:40.56022+00:00
-- url     : https://prove2.me/submissions/ea5b07a9-02a0-4b28-9ca5-55881f02704c

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Ring.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_BlockRows
import Theorems.Thm_ThreeSum_BlockRows_join_card_of_balance

set_option autoImplicit false
open ThreeSum ThreeSum.BlockRows
open Finset
open scoped BigOperators
namespace ThreeSum.BlockRows
theorem _root_.solution {J L h : ℕ} (I : Finset (Fin J))
    (Q u : Fin J → Finset (Fin L)) (hQ : ∀ i, (Q i).card = 2 * h)
    (hu : ∀ i ∈ I, u i ⊆ Q i ∧ (u i).card = h) :
    (join Iᶜ Q).card =
      (J * h - (join I u).card) +
      (J * h - (join I (fun i => Q i \ u i)).card) := by
  have hU := join_card_of_balance I u (fun i hi => (hu i hi).2)
  have hV := join_card_of_balance (h := h) I (fun i => Q i \ u i) (fun i hi => by
    rw [Finset.card_sdiff_of_subset (hu i hi).1, hQ i, (hu i hi).2]
    omega)
  have hR := join_card_of_balance Iᶜ Q (fun i _ => hQ i)
  have hcompl : Iᶜ.card = J - I.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hU, hV, hR, hcompl, ← Nat.sub_mul]
  ring
end ThreeSum.BlockRows
