-- Prove2me | solution 1 for Stallings.flowerWalk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:14:09.397681+00:00
-- url     : https://prove2.me/submissions/8892613e-8b43-4a00-918f-e1d3b61bf885

import Definitions.Def_Stallings_Folding
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Definitions.Def_Stallings_Flower
import Theorems.Thm_Stallings_CosetEquivalent_symm
import Theorems.Thm_Stallings_CosetEquivalent_trans
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff


section
namespace Stallings
private theorem flowerPos_zero (S : List Word) (i : Fin S.length) :
    flowerPos S i 0 (Nat.zero_le _) = none := by
  simp [flowerPos]
private theorem flowerWalkAux (S : List Word) (i : Fin S.length) :
    ∀ (k : Nat) (suffix : Word) (hk : k ≤ (S.get i).length),
      (S.get i).drop k = suffix →
      (flowerGraph S).Walk (flowerPos S i k hk) suffix none := by
  intro k suffix hk hdrop
  induction suffix generalizing k with
  | nil =>
      have hlen : (S.get i).length ≤ k := by
        by_contra hnot
        have hlt : k < (S.get i).length := Nat.lt_of_not_ge hnot
        have hcons := List.drop_eq_getElem_cons (l := S.get i) hlt
        rw [hdrop] at hcons
        simp at hcons
        exact hnot hcons
      have hkEq : k = (S.get i).length := le_antisymm hk hlen
      subst k
      simpa [flowerPos] using (InverseMultigraph.Walk.nil (G := flowerGraph S) none)
  | cons x xs ih =>
      have hlt : k < (S.get i).length := by
        by_contra hnot
        have hlen : (S.get i).length ≤ k := Nat.le_of_not_gt hnot
        rw [List.drop_eq_nil_of_le hlen] at hdrop
        contradiction
      have hdropCons : (S.get i).drop k =
          (S.get i).get ⟨k, hlt⟩ :: (S.get i).drop (k + 1) :=
        List.drop_eq_getElem_cons hlt
      have hparts := hdrop.symm.trans hdropCons
      rcases List.cons.inj hparts with ⟨rfl, htail⟩
      have hkNext : k + 1 ≤ (S.get i).length := Nat.succ_le_of_lt hlt
      let j : Fin (S.get i).length := ⟨k, hlt⟩
      have hsource : flowerSource S i j = flowerPos S i k hk := by
        simp [flowerSource, j]
      have htarget : flowerTarget S i j = flowerPos S i (k + 1) hkNext := by
        simp [flowerTarget, j]
      have hedge : flowerTarget S i j ∈ (flowerGraph S).edges
          (flowerSource S i j) (flowerLabel S i j) := by
        change flowerTarget S i j ∈
          (Finset.univ.filter (flowerEdge S (flowerSource S i j) (flowerLabel S i j)))
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact ⟨i, j, Or.inl ⟨rfl, rfl, rfl⟩⟩
      rw [hsource, htarget] at hedge
      have htailWalk := ih (k + 1) hkNext htail.symm
      exact InverseMultigraph.Walk.cons (G := flowerGraph S) hedge htailWalk
end Stallings
end

set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution (S : List Word) (i : Fin S.length) :
    (flowerGraph S).Walk none (S.get i) none := by
  have h := flowerWalkAux S i 0 (S.get i) (Nat.zero_le _) List.drop_zero
  simpa [flowerPos_zero] using h
end Stallings
