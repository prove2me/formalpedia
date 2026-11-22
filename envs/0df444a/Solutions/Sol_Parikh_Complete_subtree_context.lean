-- Prove2me | solution 1 for Parikh.Complete.subtree_context
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:58.096851+00:00
-- url     : https://prove2.me/submissions/758c1ccb-0f55-4285-9738-a49d8919d631

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Theorems.Thm_Parikh_ParseTree_plug_of_holes_eq_nil

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
namespace Parikh
namespace Complete
theorem _root_.solution {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Complete g t) (q : List ℕ) (u : ParseTree T g.NT)
    (hpos : t.subtree q = some u) (A : g.NT) (hu : u.root = .nonterminal A) :
    Complete g u ∧ ∃ E, OneHole g E A ∧ E.root = t.root ∧ E.plug u = t ∧
      ∀ v, t.replaceAt q v = some (E.plug v) := by
  induction q generalizing t with
  | nil =>
    simp only [ParseTree.subtree, Option.some.injEq] at hpos
    subst u
    refine ⟨ht, .hole A, ⟨.hole A, by simp [ParseTree.holes]⟩, ?_, ?_, ?_⟩
    · exact hu.symm
    · simp [ParseTree.plug]
    · intro v; simp [ParseTree.replaceAt, ParseTree.plug]
  | cons i q ih =>
    cases t with
    | terminal a => simp [ParseTree.subtree] at hpos
    | hole B => simp [ParseTree.subtree] at hpos
    | node r cs =>
      obtain ⟨c, hi, hpos⟩ := Option.bind_eq_some_iff.mp hpos
      have hcmem := List.mem_of_getElem? hi
      obtain ⟨hv, hh⟩ := ht
      cases hv with
      | node _ _ hr hc roots =>
        have hholes : ∀ d ∈ cs, d.holes = [] := by
          simpa only [ParseTree.holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hh
        obtain ⟨huc, E, hE, hroot, hplug, hreplace⟩ :=
          ih ⟨hc c hcmem, hholes c hcmem⟩ hpos
        obtain ⟨hlt, helem⟩ := List.getElem?_eq_some_iff.mp hi
        have hset : cs.set i c = cs := by rw [← helem]; exact List.set_getElem_self hlt
        have hmaps (v : ParseTree T g.NT) : cs.map (fun d => d.plug v) = cs := by
          have hm : cs.map (fun d => d.plug v) = cs.map id :=
            List.map_congr_left (fun d hd => d.plug_of_holes_eq_nil v (hholes d hd))
          simpa using hm
        refine ⟨huc, .node r (cs.set i E), ⟨?_, ?_⟩, rfl, ?_, ?_⟩
        · refine Valid.node r _ hr ?_ ?_
          · intro d hd
            rcases List.mem_or_eq_of_mem_set hd with hd | rfl
            · exact hc d hd
            · exact hE.1
          · rw [List.map_set, hroot, ← roots]
            simpa only [List.map_set] using congrArg (List.map ParseTree.root) hset
        · have hprefix : ((cs.take i).map ParseTree.holes).flatten = [] := by
            simp only [List.flatten_eq_nil_iff, List.forall_mem_map]
            intro d hd
            exact hholes d (List.mem_of_mem_take hd)
          have hsuffix : ((cs.drop (i + 1)).map ParseTree.holes).flatten = [] := by
            simp only [List.flatten_eq_nil_iff, List.forall_mem_map]
            intro d hd
            exact hholes d (List.mem_of_mem_drop hd)
          simp only [ParseTree.holes, List.set_eq_take_append_cons_drop, if_pos hlt,
            List.map_append, List.map_cons, List.flatten_append, List.flatten_cons,
            hprefix, hsuffix, hE.2, List.nil_append, List.append_nil]
        · simp only [ParseTree.plug, List.map_set, hmaps, hplug, hset]
        · intro v
          simp [ParseTree.replaceAt, hi, hreplace v, ParseTree.plug, List.map_set, hmaps]
end Complete
end Parikh
