-- Prove2me | solution 1 for Parikh.Valid.frontier_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:03.83215+00:00
-- url     : https://prove2.me/submissions/65c00773-df7b-46c4-bf73-6b4a351079d9

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Theorems.Thm_Parikh_rewrites_append_cases

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
variable {N : Type*}
namespace Parikh
namespace Valid
theorem _root_.solution {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) {v : List (Symbol T g.NT)} (h : g.Produces t.frontier v) :
    ∃ t', Valid g t' ∧ t'.root = t.root ∧ t'.frontier = v := by
  induction ht generalizing v with
  | terminal a =>
    obtain ⟨r, hr, hs⟩ := h
    have hm := hs.nonterminal_input_mem
    simp [ParseTree.frontier] at hm
  | hole A =>
    obtain ⟨r, hr, hs⟩ := h
    have hm := hs.nonterminal_input_mem
    simp only [ParseTree.frontier, List.mem_singleton, Symbol.nonterminal.injEq] at hm
    have hv : v = r.output := by
      simp only [ParseTree.frontier] at hs
      cases hs with
      | head => simp
      | cons _ hs => exact False.elim (by simpa using hs.nonterminal_input_mem)
    let leaf : Symbol T g.NT → ParseTree T g.NT := fun s => match s with
      | .terminal a => .terminal a
      | .nonterminal B => .hole B
    have hroot : ∀ s, (leaf s).root = s := by intro s; cases s <;> rfl
    refine ⟨.node r (r.output.map leaf), .node _ _ hr ?_ ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      cases s with
      | terminal a => exact .terminal a
      | nonterminal B => exact .hole B
    · simp only [List.map_map]
      simp only [Function.comp_def, hroot, List.map_id']
    · simpa only [ParseTree.root] using congrArg Symbol.nonterminal hm
    · have hf : ∀ s, (leaf s).frontier = [s] := by
        intro s; cases s <;> simp [leaf, ParseTree.frontier]
      simp only [ParseTree.frontier, List.map_map, Function.comp_def, hf]
      simpa only [← List.flatMap_def, List.flatMap_singleton'] using hv.symm
  | node r children hr hc roots ih =>
    have forest : ∀ v, g.Produces (children.map ParseTree.frontier).flatten v →
        ∃ children' : List (ParseTree T g.NT), (∀ c ∈ children', Valid g c) ∧
          children'.map ParseTree.root = children.map ParseTree.root ∧
          (children'.map ParseTree.frontier).flatten = v := by
      clear hr roots h
      induction children with
      | nil =>
        intro v hv
        obtain ⟨s, hs, hrewrite⟩ := hv
        exact False.elim (by simpa using hrewrite.nonterminal_input_mem)
      | cons c cs hcs =>
        intro v hv
        obtain ⟨s, hs, hrewrite⟩ := hv
        simp only [List.map_cons, List.flatten_cons] at hrewrite
        rcases rewrites_append_cases s c.frontier (cs.map ParseTree.frontier).flatten v
          hrewrite with ⟨u, hu, hv⟩ | ⟨u, hu, hv⟩
        · obtain ⟨c', hc', hroot, hf⟩ := ih c (by simp) ⟨s, hs, hu⟩
          refine ⟨c' :: cs, ?_, ?_, ?_⟩
          · intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hc'
            · exact hc d (by simp [hd])
          · simp only [List.map_cons, hroot]
          · simp only [List.map_cons, List.flatten_cons, hf, hv]
        · obtain ⟨cs', hvalid, hroot, hf⟩ := hcs
            (fun d hd => hc d (by simp [hd]))
            (fun d hd => ih d (by simp [hd])) u ⟨s, hs, hu⟩
          refine ⟨c :: cs', ?_, ?_, ?_⟩
          · intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hc d (by simp)
            · exact hvalid d hd
          · simp only [List.map_cons, hroot]
          · simp only [List.map_cons, List.flatten_cons, hf, hv]
    obtain ⟨children', hvalid, hroots, hf⟩ := forest v (by
      simpa only [ParseTree.frontier] using h)
    exact ⟨.node r children', .node _ _ hr hvalid (hroots.trans roots),
      rfl, by simpa only [ParseTree.frontier] using hf⟩
end Valid
end Parikh
