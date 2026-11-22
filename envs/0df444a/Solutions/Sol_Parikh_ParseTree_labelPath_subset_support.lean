-- Prove2me | solution 1 for Parikh.ParseTree.labelPath_subset_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:45.725806+00:00
-- url     : https://prove2.me/submissions/2d059456-fa0e-4e87-862b-087c456ed2b3

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths

set_option autoImplicit true
@[expose] public section
public section
open Parikh Parikh.ParseTree
variable {T N : Type*}
namespace Parikh.ParseTree
theorem _root_.solution (t : ParseTree T N) (path : List N)
    (hpath : path ∈ t.labelPaths) : ∀ A ∈ path, A ∈ t.support := by
  induction t using ParseTree.rec (motive_2 := fun cs =>
    ∀ c ∈ cs, ∀ path ∈ c.labelPaths, ∀ A ∈ path, A ∈ c.support) generalizing path with
  | terminal a =>
    simp only [labelPaths, List.mem_singleton] at hpath
    subst path
    simp
  | hole A =>
    simp only [labelPaths, List.mem_singleton] at hpath
    subst path
    simp
  | node r cs ih =>
    simp only [labelPaths, List.mem_cons, List.mem_map, ← List.flatMap_def,
      List.mem_flatMap] at hpath
    rcases hpath with rfl | ⟨tail, ⟨c, hc, htail⟩, rfl⟩
    · intro A hA
      have heq : A = r.input := by simpa using hA
      simp [support, productionLabels, heq]
    · intro A hA
      simp only [List.mem_cons] at hA
      rcases hA with rfl | hA
      · simp [support, productionLabels]
      · have hchild := ih c hc tail htail A hA
        simp only [support, productionLabels, Set.mem_ofPred_eq, List.mem_cons,
          ← List.flatMap_def, List.mem_flatMap]
        exact Or.inr ⟨c, hc, hchild⟩
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rename_i path hp A hA
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc path hp A hA
    · exact hcs d hd path hp A hA
end Parikh.ParseTree
