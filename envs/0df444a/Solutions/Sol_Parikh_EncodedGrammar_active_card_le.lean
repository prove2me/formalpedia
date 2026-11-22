-- Prove2me | solution 1 for Parikh.EncodedGrammar.active_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:11.006369+00:00
-- url     : https://prove2.me/submissions/389af901-9ff6-4ad1-897a-ee2ea8042ac1

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
theorem _root_.solution (g : EncodedGrammar) :
    (activeNonterminals g.decode).card ≤ g.size.nonterminals := by
  classical
  calc
    (activeNonterminals g.decode).card = g.activeLabels.card :=
      congrArg Finset.card g.activeLabels_eq.symm
    _ ≤ Fintype.card (Fin (g.extraNonterminalCount + 1)) := Finset.card_le_univ _
    _ = g.size.nonterminals := by simp [size]
end Parikh.EncodedGrammar
