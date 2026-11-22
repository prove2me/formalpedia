-- Prove2me | solution 1 for Parikh.EncodedGrammar.cycleTest_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:11.647306+00:00
-- url     : https://prove2.me/submissions/cf361220-2f7a-45cc-9197-00b67290909e

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
public import Theorems.Thm_Parikh_EncodedGrammar_activeLabels_eq

set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar
namespace Parikh.EncodedGrammar
theorem _root_.solution (g : EncodedGrammar)
    (C : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
    (hv : Valid g.decode C) : g.cycleTest C = true ↔ IsBoundedCycle g.decode C := by
  unfold cycleTest
  rw [activeLabels_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨A, hh, hr, hp⟩, hheight⟩
    exact ⟨⟨A, ⟨hv, hh⟩, hr, hp⟩, hheight⟩
  · rintro ⟨⟨A, ⟨_, hh⟩, hr, hp⟩, hheight⟩
    exact ⟨⟨A, hh, hr, hp⟩, hheight⟩
end Parikh.EncodedGrammar
