-- Prove2me | solution 1 for Parikh.EncodedGrammar.mem_baseTrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:54.288085+00:00
-- url     : https://prove2.me/submissions/ce2cfd64-41cd-4de7-8a06-9cbc2fa4f9f2

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
public import Theorems.Thm_Parikh_EncodedGrammar_activeLabels_eq
public import Theorems.Thm_Parikh_EncodedGrammar_baseTest_correct
public import Theorems.Thm_Parikh_simple_height


set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar
namespace Parikh.EncodedGrammar
theorem _root_.solution (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :
    B ∈ g.baseTrees ↔ IsBase g.decode B := by
  let _ := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  change B ∈ ((boundedEnumeration.enumerate g (g.activeLabels.card + 1)).filter
    g.baseTest).dedup ↔ _
  rw [List.mem_dedup, List.mem_filter]
  constructor
  · rintro ⟨hm, ht⟩
    exact (g.baseTest_correct B ((boundedEnumeration.correct g _ B).mp hm).1).mp ht
  · intro hb
    have hh : B.height ≤ g.activeLabels.card := by
      rw [g.activeLabels_eq]
      exact simple_height g.decode B hb.1 hb.2.2
    exact ⟨(boundedEnumeration.correct g _ B).mpr ⟨hb.1.1, hh.trans (Nat.le_succ _)⟩,
      (g.baseTest_correct B hb.1.1).mpr hb⟩
end Parikh.EncodedGrammar
