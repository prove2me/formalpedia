-- Prove2me | solution 1 for SimpleGraph.degreeWithin_add_degreeWithin_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:01.153058+00:00
-- url     : https://prove2.me/submissions/00793e0d-1130-4811-9f7a-e1b526194e2f

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {S : Finset V} {v : V} (hv : v ∈ S) :
    G.degreeWithin S v + Gᶜ.degreeWithin S v + 1 = #S := by
  have h1 : {w ∈ S | Gᶜ.Adj v w} = {w ∈ S.erase v | ¬G.Adj v w} := by
    ext w
    simp only [mem_filter, mem_erase, compl_adj]
    exact ⟨fun ⟨hw, hne, hna⟩ => ⟨⟨Ne.symm hne, hw⟩, hna⟩,
      fun ⟨⟨hne, hw⟩, hna⟩ => ⟨hw, Ne.symm hne, hna⟩⟩
  have h2 : {w ∈ S | G.Adj v w} = {w ∈ S.erase v | G.Adj v w} := by
    ext w
    simp only [mem_filter, mem_erase]
    exact ⟨fun ⟨hw, ha⟩ => ⟨⟨(G.ne_of_adj ha).symm, hw⟩, ha⟩, fun ⟨⟨_, hw⟩, ha⟩ => ⟨hw, ha⟩⟩
  rw [degreeWithin, degreeWithin, h1, h2, card_filter_add_card_filter_not, card_erase_of_mem hv]
  have : 0 < #S := card_pos.mpr ⟨v, hv⟩
  omega
end SimpleGraph
