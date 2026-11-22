-- Prove2me | solution 1 for Parikh.EncodedGrammar.cycleTrees_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:44.661049+00:00
-- url     : https://prove2.me/submissions/182dd8f1-a67a-43e0-bd7f-c1ae5f6028cc

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
theorem _root_.solution (g : EncodedGrammar) : g.cycleTrees.Nodup := by
  let _ := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  unfold cycleTrees
  exact List.nodup_dedup _
end Parikh.EncodedGrammar
