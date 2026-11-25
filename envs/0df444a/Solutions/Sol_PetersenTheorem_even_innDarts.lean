-- Prove2me | solution 1 for PetersenTheorem.even_innDarts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:12:57.265503+00:00
-- url     : https://prove2.me/submissions/8c67f7e8-497c-4bf2-82ea-a7a86b4b0558

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace PetersenTheorem
theorem _root_.solution (C : Finset V) : Even (innDarts G C) := by
  classical
  let H : SimpleGraph V :=
    { Adj := fun x y => G.Adj x y ∧ x ∈ C ∧ y ∈ C
      symm := ⟨fun x y h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
  have hdeg : ∀ x, H.degree x = if x ∈ C then (G.neighborFinset x ∩ C).card else 0 := by
    intro x
    rw [← card_neighborFinset_eq_degree]
    split_ifs with hx
    · congr 1
      ext y
      simp [H, hx]
    · rw [Finset.card_eq_zero]
      ext y
      simp [H, hx]
  have hsum := H.sum_degrees_eq_twice_card_edges
  simp only [hdeg] at hsum
  rw [Finset.sum_ite_mem, Finset.univ_inter] at hsum
  unfold innDarts
  rw [hsum]
  exact even_two_mul _
end PetersenTheorem
