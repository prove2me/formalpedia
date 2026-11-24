-- Prove2me | solution 1 for Stallings.basisRose_loopSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:01.214972+00:00
-- url     : https://prove2.me/submissions/a029629a-c12f-472b-b747-188e0513695f

import Definitions.Def_Stallings_InverseAutomaton
import Definitions.Def_Stallings_BasisRose
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff


section
namespace Stallings
private theorem wordEval_pos (i : Fin 2) :
    wordEval [(i, true)] = FreeGroup.of i := by
  rfl
private theorem wordEval_neg (i : Fin 2) :
    wordEval [(i, false)] = (FreeGroup.of i)⁻¹ := by
  simp [wordEval, FreeGroup.of, FreeGroup.invRev]
private theorem basisRose_walk_mem (S : Finset (Fin 2)) {v z : Fin 1} {w : Word}
    (h : (basisRose S).Walk v w z) : wordEval w ∈ basisSubgroup S := by
  induction h with
  | nil v =>
      change (FreeGroup.mk [] : Free) ∈ basisSubgroup S
      rw [← FreeGroup.one_eq_mk]
      exact (basisSubgroup S).one_mem
  | @cons v u z x w edge tail ih =>
      have hv : v = (0 : Fin 1) := Subsingleton.elim _ _
      subst v
      have hu : u = (0 : Fin 1) := Subsingleton.elim _ _
      subst u
      have hz : z = (0 : Fin 1) := Subsingleton.elim _ _
      subst z
      have hi : x.1 ∈ S := by
        have hedge : (basisRose S).next 0 x = some (0 : Fin 1) := by
          simpa using edge
        simpa [basisRose] using hedge
      have hgen : FreeGroup.of x.1 ∈ basisSubgroup S :=
        Subgroup.subset_closure ⟨x.1, hi, rfl⟩
      have hletter : wordEval [x] ∈ basisSubgroup S := by
        rcases x with ⟨i, b⟩
        cases b
        · rw [wordEval_neg]
          exact (basisSubgroup S).inv_mem hgen
        · rw [wordEval_pos]
          exact hgen
      have hsplit : wordEval (x :: w) = wordEval [x] * wordEval w := by
        rw [show x :: w = [x] ++ w by rfl, wordEval_append]
      rw [hsplit]
      exact (basisSubgroup S).mul_mem hletter ih
end Stallings
end

set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution (S : Finset (Fin 2)) :
    (basisRose S).loopSubgroup = basisSubgroup S := by
  apply le_antisymm
  · intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    rw [← hw]
    exact basisRose_walk_mem S hwalk
  · apply (Subgroup.closure_le ((basisRose S).loopSubgroup)).2
    intro g hg
    rcases hg with ⟨i, hi, rfl⟩
    have hiFin : i ∈ S := by simpa using hi
    refine ⟨[(i, true)], ?_, ?_⟩
    · exact wordEval_pos i
    · have hedge : (basisRose S).next 0 (i, true) = some (0 : Fin 1) := by
        simp [basisRose, hiFin]
      exact InverseAutomaton.Walk.cons hedge (InverseAutomaton.Walk.nil 0)
end Stallings
