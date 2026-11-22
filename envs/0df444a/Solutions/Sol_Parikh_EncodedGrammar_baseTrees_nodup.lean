-- Prove2me | solution 1 for Parikh.EncodedGrammar.baseTrees_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:51.465333+00:00
-- url     : https://prove2.me/submissions/63b7a3e4-964a-4a83-83a2-ae5338121ba4

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
theorem _root_.solution (g : EncodedGrammar) : g.baseTrees.Nodup := by
  let _ := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  unfold baseTrees
  exact List.nodup_dedup _
end Parikh.EncodedGrammar
