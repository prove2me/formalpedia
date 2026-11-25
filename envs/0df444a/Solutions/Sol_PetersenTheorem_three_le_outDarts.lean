-- Prove2me | solution 1 for PetersenTheorem.three_le_outDarts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:22:03.022804+00:00
-- url     : https://prove2.me/submissions/d3756217-f1af-410f-9683-bb66d71e15d7

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Theorems.Thm_PetersenTheorem_even_innDarts
public import Theorems.Thm_PetersenTheorem_outDarts_add_innDarts
public import Theorems.Thm_PetersenTheorem_outDarts_ne_one

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace PetersenTheorem
theorem _root_.solution (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (C : Finset V) (hC : Odd C.card) : 3 ≤ outDarts G C := by
  have h1 := outDarts_add_innDarts G h3 C
  have h2 := even_innDarts G C
  have h4 := outDarts_ne_one G hb C
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := hC
  omega
end PetersenTheorem
