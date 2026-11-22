-- Prove2me | solution 1 for Parikh.EncodedGrammar.baseTest_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:54.798124+00:00
-- url     : https://prove2.me/submissions/d581368d-5e79-4f1c-a628-5818bb218173

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees

set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar
namespace Parikh.EncodedGrammar
theorem _root_.solution (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
    (hv : Valid g.decode B) : g.baseTest B = true ↔ IsBase g.decode B := by
  unfold baseTest
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨hh, hr⟩, hs⟩
    exact ⟨⟨hv, hh⟩, hr, hs⟩
  · rintro ⟨⟨_, hh⟩, hr, hs⟩
    exact ⟨⟨hh, hr⟩, hs⟩
end Parikh.EncodedGrammar
