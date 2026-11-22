-- Prove2me | solution 1 for Parikh.EncodedGrammar.mem_cycleTrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:47.744793+00:00
-- url     : https://prove2.me/submissions/e60533cc-2890-497e-b7dd-40f0ecd9f5c4

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
public import Theorems.Thm_Parikh_EncodedGrammar_activeLabels_eq
public import Theorems.Thm_Parikh_EncodedGrammar_cycleTest_correct

set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar
namespace Parikh.EncodedGrammar
theorem _root_.solution (g : EncodedGrammar)
    (C : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :
    C ∈ g.cycleTrees ↔ IsBoundedCycle g.decode C := by
  let _ := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  change C ∈ ((boundedEnumeration.enumerate g (g.activeLabels.card + 1)).filter
    g.cycleTest).dedup ↔ _
  rw [List.mem_dedup, List.mem_filter]
  constructor
  · rintro ⟨hm, ht⟩
    exact (g.cycleTest_correct C ((boundedEnumeration.correct g _ C).mp hm).1).mp ht
  · intro hc
    obtain ⟨A, ha⟩ := hc.1
    have hh : C.height ≤ g.activeLabels.card + 1 := by
      rw [g.activeLabels_eq]
      exact hc.2
    exact ⟨(boundedEnumeration.correct g _ C).mpr ⟨ha.1.1, hh⟩,
      (g.cycleTest_correct C ha.1.1).mpr hc⟩
end Parikh.EncodedGrammar
