-- Prove2me | solution 1 for Parikh.ParseTree.exists_labelPath_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:19.865012+00:00
-- url     : https://prove2.me/submissions/10200b5c-0c37-4778-904d-c3d96fa0dae0

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths

set_option autoImplicit true
@[expose] public section
public section
open Parikh Parikh.ParseTree
variable {T N : Type*}
namespace Parikh.ParseTree
theorem _root_.solution (t : ParseTree T N) :
    ∃ path ∈ t.labelPaths, path.length = t.height := by
  induction t using ParseTree.rec (motive_2 := fun cs =>
    ∀ c ∈ cs, ∃ path ∈ c.labelPaths, path.length = c.height) with
  | terminal a => exact ⟨[], by simp [labelPaths], by simp [height]⟩
  | hole A => exact ⟨[], by simp [labelPaths], by simp [height]⟩
  | node r cs ih =>
    by_cases hcs : cs = []
    · subst cs
      exact ⟨[r.input], by simp [labelPaths], by simp [height]⟩
    · have hheights : cs.map height ≠ [] := fun h => hcs (List.map_eq_nil_iff.mp h)
      obtain ⟨c, hc, hmax⟩ := List.mem_map.mp (List.max_mem hheights)
      obtain ⟨path, hp, hlen⟩ := ih c hc
      refine ⟨r.input :: path, ?_, ?_⟩
      · simp only [labelPaths, List.mem_cons, List.mem_map, ← List.flatMap_def,
          List.mem_flatMap]
        exact Or.inr ⟨path, ⟨c, hc, hp⟩, rfl⟩
      · simp only [List.length_cons, height, List.foldl_max_eq_max hheights,
          Nat.zero_max, hlen, hmax]
        omega
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd
end Parikh.ParseTree
