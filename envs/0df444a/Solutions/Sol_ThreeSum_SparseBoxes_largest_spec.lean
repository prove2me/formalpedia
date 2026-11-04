-- Prove2me | solution 1 for ThreeSum.SparseBoxes.largest_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:54.212093+00:00
-- url     : https://prove2.me/submissions/2d63e88e-7567-4a79-a232-4cd33bb3e578

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

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (t : ℕ) (m : Finset α) (h : t ≤ m.card) :
    IsLargest t m (largest t m) := by
  induction t generalizing m with
  | zero => simp [largest, IsLargest]
  | succ t ih =>
      have hm : m.Nonempty := Finset.card_pos.mp (by omega)
      let a := m.max' hm
      have ha : a ∈ m := Finset.max'_mem m hm
      have hcard : (m.erase a).card = m.card - 1 := Finset.card_erase_of_mem ha
      have ht : t ≤ (m.erase a).card := by omega
      obtain ⟨hsub, hsize, horder⟩ := ih (m.erase a) ht
      have hnot : a ∉ largest t (m.erase a) := by
        intro hx
        exact Finset.notMem_erase a m (hsub hx)
      simp only [largest, dif_pos hm]
      change IsLargest (t + 1) m (insert a (largest t (m.erase a)))
      refine ⟨Finset.insert_subset ha (hsub.trans (Finset.erase_subset a m)), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hnot, hsize]
      · intro u hu x hx hnx
        have hxa : x ≠ a := by
          intro he
          apply hnx
          simp [he]
        have hxe : x ∈ m.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
        rcases Finset.mem_insert.mp hu with hua | hut
        · subst u
          exact Finset.lt_max'_of_mem_erase_max' m hm hxe
        · apply horder u hut x hxe
          intro hxt
          exact hnx (Finset.mem_insert_of_mem hxt)
end ThreeSum.SparseBoxes
