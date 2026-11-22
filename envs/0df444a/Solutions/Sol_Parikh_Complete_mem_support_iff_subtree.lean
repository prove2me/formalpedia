-- Prove2me | solution 1 for Parikh.Complete.mem_support_iff_subtree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:03.759403+00:00
-- url     : https://prove2.me/submissions/86f1fd4b-de7d-4568-884b-64297286e97c

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreeReplacement

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
namespace Parikh
namespace Complete
theorem _root_.solution {g : ContextFreeGrammar T}
    {t : ParseTree T g.NT} (ht : Complete g t) (A : g.NT) :
    A ∈ t.support ↔ ∃ q u, t.subtree q = some u ∧ u.root = .nonterminal A := by
  obtain ⟨hv, hh⟩ := ht
  induction hv with
  | terminal a =>
    simp only [ParseTree.support, ParseTree.productionLabels, Set.mem_ofPred_eq,
      List.not_mem_nil, false_iff]
    rintro ⟨q, u, hq, hu⟩
    cases q with
    | nil => simp [ParseTree.subtree] at hq; subst u; simp [ParseTree.root] at hu
    | cons i q => simp [ParseTree.subtree] at hq
  | hole B => simp [ParseTree.holes] at hh
  | node r cs hr hc roots ih =>
    have hholes : ∀ c ∈ cs, c.holes = [] := by
      simpa only [ParseTree.holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hh
    simp only [ParseTree.support, ParseTree.productionLabels, Set.mem_ofPred_eq,
      List.mem_cons, ← List.flatMap_def, List.mem_flatMap]
    constructor
    · rintro (hA | ⟨c, hcmem, hA⟩)
      · subst A
        exact ⟨[], .node r cs, rfl, rfl⟩
      · obtain ⟨q, u, hq, hu⟩ := (ih c hcmem (hholes c hcmem)).mp hA
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcmem
        exact ⟨i :: q, u, by simp [ParseTree.subtree, hi, hq], hu⟩
    · rintro ⟨q, u, hq, hu⟩
      cases q with
      | nil =>
        simp only [ParseTree.subtree, Option.some.injEq] at hq
        subst u
        exact Or.inl (by simpa only [ParseTree.root, Symbol.nonterminal.injEq] using hu.symm)
      | cons i q =>
        obtain ⟨c, hi, hq⟩ := Option.bind_eq_some_iff.mp hq
        have hcmem := List.mem_of_getElem? hi
        exact Or.inr ⟨c, hcmem, (ih c hcmem (hholes c hcmem)).mpr ⟨q, u, hq, hu⟩⟩
end Complete
end Parikh
