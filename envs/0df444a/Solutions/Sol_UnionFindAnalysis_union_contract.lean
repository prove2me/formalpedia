-- Prove2me | solution 1 for UnionFindAnalysis.union_contract
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:56:34.125223+00:00
-- url     : https://prove2.me/submissions/2288be2d-d2ff-476e-93a9-86b487ab2fa7

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_valid


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Union-find mathematics for implementations using union by rank.

The parent and rank maps describe the stored data. Representatives and masses
are proof-only witnesses: a root owns the mass of its component, and linking
two roots transfers all losing mass to the winner. Starting from singleton
components gives a fixed mass budget of `n`. A root of rank `r` owns at least
`2 ^ r` mass, so every find follows at most `log₂ n` parent links.

Path compression preserves these bounds and the represented partition. The
module proves a logarithmic worst-case bound, not an inverse-Ackermann amortized
bound. It imports no generated algorithm or execution model.
-/

namespace Algo2Lean.UnionFind











theorem entry_le_total {n : Nat} (f : Fin n → Nat) (vertex : Fin n) :
    f vertex ≤ total f := by
  induction n with
  | zero => exact Fin.elim0 vertex
  | succ n ih =>
    refine Fin.cases ?_ (fun index => ?_) vertex
    · simp [total]
    · have bound := ih (fun index => f index.succ) index
      change f index.succ ≤ f 0 + total (fun index => f index.succ)
      omega

















theorem find_correct {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (run : Find state vertex root steps) :
    root = state.representative vertex ∧ state.parent root = root ∧
      state.rank vertex + steps ≤ state.rank root := by
  induction run with
  | root vertex fixed => exact ⟨(valid.root_representative vertex fixed).symm, fixed, by simp⟩
  | step vertex root steps moving _ ih =>
    obtain ⟨correct, fixed, bound⟩ := ih
    have rising := valid.parent_rank vertex moving
    exact ⟨correct.trans (valid.parent_representative vertex), fixed, by omega⟩





/-- Every valid forest admits a finite find traversal. -/
theorem find_exists {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) : ∃ steps, Find state vertex (state.representative vertex) steps := by
  by_cases fixed : state.parent vertex = vertex
  · exact ⟨0, by simpa [valid.root_representative vertex fixed] using Find.root vertex fixed⟩
  · obtain ⟨steps, run⟩ := find_exists valid (state.parent vertex)
    exact ⟨steps + 1, Find.step vertex _ steps fixed
      (by simpa [valid.parent_representative vertex] using run)⟩
termination_by total state.rank - state.rank vertex
decreasing_by
  have rising := valid.parent_rank vertex fixed
  have bounded := entry_le_total state.rank (state.parent vertex)
  omega









































end Algo2Lean.UnionFind

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Reusable contracts for the compiled union-find implementation.

`find_contract` and `union_contract` give the exact model, storage, and clock
effects of full path compression and union by rank. `find_amortized` and
`union_amortized` bound incremental work using a shared inverse-Ackermann
potential. The simpler `find_summary` and `union_summary` retain logarithmic
worst-case bounds, partition guarantees, and protection for caller storage.

The forest and rank invariants are independent of generated code and graphs.
Constructor correctness is in the companion `union_find_init` analysis. Costs
count the explicit source clocks and compose from arbitrary initial counters.
-/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated













/-- Counts reflect every recursive lookup and every parent-pointer rewrite. -/
theorem findHeap_clocks (heap : Heap) (parent : SeqRef) (vertex root : Int)
    (length : Nat) (clock : String) :
    (findHeap heap parent vertex root length).clocks clock = heap.clocks clock +
      (if clock = "uf_find" then length + 1 else 0) +
      (if clock = "uf_compress" then length else 0) := by
  induction length generalizing heap vertex with
  | zero => by_cases same : clock = "uf_find" <;> simp [findHeap, Heap.tick, same]
  | succ length ih =>
    simp only [findHeap, Heap.tick, Heap.write]
    rw [ih]
    by_cases first : clock = "uf_find" <;> by_cases second : clock = "uf_compress" <;>
      simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Lookup follows a finite parent path and compresses it on return. It can run
    beneath any caller stack and requires no graph-specific invariant. -/
theorem find_path (length : Nat) (heap : Heap) (object : Ref_UnionFind) (parent : SeqRef)
    (vertex root : Int) (valid : is_UnionFind heap object)
    (readParent : field_UnionFind_parent heap object = some parent)
    (allocated : parent < heap.nextRef)
    (path : ParentPath (heap.read parent) vertex root length) :
    UnionFind.find.Call heap (object, vertex) (findHeap heap parent vertex root length) root := by
  induction length generalizing heap vertex with
  | zero =>
    cases path with
    | root vertex fixed =>
      refine ⟨valid, ?_⟩
      intro caller
      apply Reaches.prepend (Step.UnionFind_find_pc15 _ _ _ (by simp [readParent]))
      apply Reaches.prepend (Step.UnionFind_find_pc14 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc13 _ _ _ (by simpa [readParent] using allocated))
      apply Reaches.prepend (Step.UnionFind_find_pc12_true _ _ _ (by simpa [readParent] using fixed))
      apply Reaches.prepend (Step.UnionFind_find_pc11 _ _ _)
      exact Reaches.single (Step.UnionFind_find_pc10 _ _ _)
  | succ length ih =>
    cases path with
    | next vertex root _ different tail =>
      have recursive := ih (heap.tick "uf_find") (heap.read parent vertex) valid readParent allocated tail
      refine ⟨valid, ?_⟩
      intro caller
      apply Reaches.prepend (Step.UnionFind_find_pc15 _ _ _ (by simp [readParent]))
      apply Reaches.prepend (Step.UnionFind_find_pc14 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc13 _ _ _ (by simpa [readParent] using allocated))
      apply Reaches.prepend (Step.UnionFind_find_pc12_false _ _ _ (by simpa [readParent] using different))
      apply Reaches.prepend (Step.UnionFind_find_pc9 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc8 _ _ _ valid)
      apply Reaches.prepend (Step.UnionFind_find_pc7 _ _ _ (by simpa [readParent] using allocated))
      apply Reaches.prepend (Step.UnionFind_find_pc6 _ _ _)
      simp only [readParent, Option.getD_some]
      apply (recursive.2 _).trans
      apply Reaches.prepend (Step.UnionFind_find_pc5 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc4 _ _ _ (by simpa using allocated))
      apply Reaches.prepend (Step.UnionFind_find_pc3 _ _ _)
      apply Reaches.prepend (Step.UnionFind_find_pc2 _ _ _)
      exact Reaches.single (Step.UnionFind_find_pc1 _ _ _)


open Algo2Lean.UnionFind (State Find compress compress_valid find_correct  find_exists)





/-- Charging a clock does not change the represented data structure. -/
theorem Rep.tick {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (clock : String) (amount : Nat := 1) :
    Rep (heap.tick clock amount) layout model :=
  ⟨representation.valid, representation.object, representation.readParent,
    representation.readRank, representation.readSize, representation.parentAllocated,
    representation.rankAllocated, representation.separate, representation.parents,
    representation.ranks⟩









/-- A compression write preserves the partition and every representation field. -/
theorem Rep.compress {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (vertex : Fin n) :
    Rep (heap.write layout.parent (vertex.val : Int) ((model.representative vertex).val : Int))
      layout (compress model vertex) := by
  refine ⟨compress_valid representation.valid vertex, representation.object,
    representation.readParent, representation.readRank, representation.readSize,
    representation.parentAllocated, representation.rankAllocated, representation.separate, ?_, ?_⟩
  · intro other
    by_cases same : other = vertex
    · subst other
      simp [Heap.read, Heap.write, Algo2Lean.UnionFind.compress, Algo2Lean.UnionFind.update]
    · have different : (other.val : Int) ≠ (vertex.val : Int) := by
        intro equal
        exact same (Fin.ext (by omega))
      simpa [Heap.read, Heap.write, Algo2Lean.UnionFind.compress, Algo2Lean.UnionFind.update, same, different] using
        representation.parents other
  · intro other
    simpa [Heap.read, Heap.write, Ne.symm representation.separate, Algo2Lean.UnionFind.compress] using
      representation.ranks other

/-- A finite model path is the same path read through the generated heap interface. -/
theorem model_path {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) {vertex root : Fin n} {length : Nat}
    (path : Find model vertex root length) :
    ParentPath (heap.read layout.parent) vertex.val root.val length := by
  induction path with
  | root vertex fixed =>
    apply ParentPath.root
    simpa [fixed] using representation.parents vertex
  | step vertex root length moving tail ih =>
    apply ParentPath.next _ _ _
    · rw [representation.parents vertex]
      intro equal
      exact moving (Fin.ext (by omega))
    · simpa [representation.parents vertex] using ih

/-- The exact operational heap after lookup represents the compressed model. -/
theorem findHeap_rep {n : Nat} {model : State n} {vertex root : Fin n} {length : Nat}
    (path : Find model vertex root length) (heap : Heap) (layout : Layout)
    (representation : Rep heap layout model) :
    Rep (findHeap heap layout.parent vertex.val root.val length)
      layout (findResult model vertex length) := by
  induction path generalizing heap with
  | root vertex fixed => exact representation.tick "uf_find"
  | step vertex root length moving tail ih =>
    have recursive := ih (heap.tick "uf_find") (representation.tick "uf_find")
    have result := (recursive.compress vertex).tick "uf_compress"
    have correct := (find_correct representation.valid (Find.step vertex root length moving tail)).1
    simpa [findHeap, findResult, representation.parents vertex, findResult_representative, correct] using! result











/-- Union composes two verified lookups with the source rank comparison and link.
    This lemma exposes only source inputs, heaps, and operation contracts. -/
theorem union_calls (before middle heap : Heap) (layout : Layout) (a b left right : Int)
    (first : UnionFind.find.Call before (layout.object,a) middle left)
    (second : UnionFind.find.Call middle (layout.object,b) heap right)
    (readParent : field_UnionFind_parent heap layout.object = some layout.parent)
    (readRank : field_UnionFind_rank heap layout.object = some layout.rank)
    (parentAllocated : layout.parent < heap.nextRef) (rankAllocated : layout.rank < heap.nextRef)
    (separate : layout.parent ≠ layout.rank) :
    UnionFind.union.Call before (layout.object,a,b) (unionHeap heap layout left right)
      (decide (left ≠ right)) := by
  refine ⟨first.1, ?_⟩
  intro caller
  apply Reaches.prepend (Step.UnionFind_union_pc25 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc24 _ _ _ (by exact first.1))
  apply Reaches.prepend (Step.UnionFind_union_pc23 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc22 _ _ _)
  apply (first.2 _).trans
  apply Reaches.prepend (Step.UnionFind_union_pc21 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc20 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc19 _ _ _ (by exact second.1))
  apply Reaches.prepend (Step.UnionFind_union_pc18 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc17 _ _ _)
  apply (second.2 _).trans
  apply Reaches.prepend (Step.UnionFind_union_pc16 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc15 _ _ _)
  apply Reaches.prepend (Step.UnionFind_union_pc14 _ _ _)
  by_cases same : left = right
  · apply Reaches.prepend (Step.UnionFind_union_pc13_true _ _ _ (by simpa using same))
    apply Reaches.prepend (Step.UnionFind_union_pc12 _ _ _)
    simpa [unionHeap, same] using Reaches.single (Step.UnionFind_union_pc11 _ _ caller)
  · apply Reaches.prepend (Step.UnionFind_union_pc13_false _ _ _ (by simpa using same))
    apply Reaches.prepend (Step.UnionFind_union_pc10 _ _ _ (by simpa [readRank] using rankAllocated))
    by_cases less : heap.read layout.rank left < heap.read layout.rank right
    · apply Reaches.prepend (Step.UnionFind_union_pc9_true _ _ _ (by simpa [readRank] using less))
      apply Reaches.prepend (Step.UnionFind_union_pc3 _ _ _ (by simpa [readParent] using parentAllocated))
      apply Reaches.prepend (Step.UnionFind_union_pc2 _ _ _)
      simpa [unionHeap, same, less, readParent] using Reaches.single (Step.UnionFind_union_pc1 _ _ caller)
    · apply Reaches.prepend (Step.UnionFind_union_pc9_false _ _ _ (by simpa [readRank] using less))
      apply Reaches.prepend (Step.UnionFind_union_pc8 _ _ _ (by simpa [readRank] using rankAllocated))
      by_cases more : heap.read layout.rank right < heap.read layout.rank left
      · apply Reaches.prepend (Step.UnionFind_union_pc7_true _ _ _ (by simpa [readRank] using more))
        apply Reaches.prepend (Step.UnionFind_union_pc4 _ _ _ (by simpa [readParent] using parentAllocated))
        apply Reaches.prepend (Step.UnionFind_union_pc2 _ _ _)
        simpa [unionHeap, same, less, more, readParent] using Reaches.single (Step.UnionFind_union_pc1 _ _ caller)
      · apply Reaches.prepend (Step.UnionFind_union_pc7_false _ _ _ (by simpa [readRank] using more))
        apply Reaches.prepend (Step.UnionFind_union_pc6 _ _ _ (by simpa [readParent] using parentAllocated))
        apply Reaches.prepend (Step.UnionFind_union_pc5 _ _ _ (by simpa [readRank] using rankAllocated))
        apply Reaches.prepend (Step.UnionFind_union_pc2 _ _ _)
        simpa [unionHeap, same, less, more, readParent, readRank, Heap.read_write_other_ref, Ne.symm separate] using Reaches.single (Step.UnionFind_union_pc1 _ _ caller)




/-- Linking exactly two roots implements the independent union-by-rank model. -/
theorem Rep.link {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (loser winner : Fin n)
    (different : loser ≠ winner) (loserRoot : model.parent loser = loser)
    (winnerRoot : model.parent winner = winner) (ordered : model.rank loser ≤ model.rank winner) :
    Rep (linkHeap heap layout loser.val winner.val) layout
      (Algo2Lean.UnionFind.link model loser winner) := by
  have valid := Algo2Lean.UnionFind.link_valid representation.valid loser winner different loserRoot winnerRoot ordered
  unfold linkHeap
  rw [representation.ranks loser, representation.ranks winner]
  by_cases tied : model.rank loser = model.rank winner
  · simp only [tied, ↓reduceIte]
    refine ⟨valid, representation.object, representation.readParent, representation.readRank,
      representation.readSize, representation.parentAllocated, representation.rankAllocated,
      representation.separate, ?_, ?_⟩
    · intro vertex
      by_cases same : vertex = loser
      · subst vertex
        simp [Heap.read, Heap.write, representation.separate, Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update]
      · have indexDifferent : (vertex.val : Int) ≠ (loser.val : Int) := by
          intro eq; exact same (Fin.ext (by omega))
        simpa [Heap.read, Heap.write, representation.separate, indexDifferent,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, same] using representation.parents vertex
    · intro vertex
      by_cases same : vertex = winner
      · subst vertex
        simp [Heap.read, Heap.write, Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, tied]
      · have indexDifferent : (vertex.val : Int) ≠ (winner.val : Int) := by
          intro eq; exact same (Fin.ext (by omega))
        simpa [Heap.read, Heap.write, Ne.symm representation.separate, indexDifferent,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, same] using representation.ranks vertex
  · have unequal : (model.rank loser : Int) ≠ (model.rank winner : Int) := by omega
    simp only [if_neg unequal]
    refine ⟨valid, representation.object, representation.readParent, representation.readRank,
      representation.readSize, representation.parentAllocated, representation.rankAllocated,
      representation.separate, ?_, ?_⟩
    · intro vertex
      by_cases same : vertex = loser
      · subst vertex
        simp [Heap.read, Heap.write, Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update]
      · have indexDifferent : (vertex.val : Int) ≠ (loser.val : Int) := by
          intro eq; exact same (Fin.ext (by omega))
        simpa [Heap.read, Heap.write, indexDifferent,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, same] using representation.parents vertex
    · intro vertex
      by_cases same : vertex = winner
      · subst vertex
        simpa [Heap.read, Heap.write, Ne.symm representation.separate,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, tied] using representation.ranks winner
      · simpa [Heap.read, Heap.write, Ne.symm representation.separate,
          Algo2Lean.UnionFind.link, Algo2Lean.UnionFind.update, tied, same] using representation.ranks vertex

/-- The source rank branches implement the pure union operation. -/
theorem unionHeap_rep {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (a b : Fin n) :
    Rep (unionHeap heap layout (model.representative a).val (model.representative b).val)
      layout (Algo2Lean.UnionFind.union model a b) := by
  let left := model.representative a
  let right := model.representative b
  have leftRoot := representation.valid.representative_root a
  have rightRoot := representation.valid.representative_root b
  change Rep (unionHeap heap layout left.val right.val) layout
    (if left = right then model else if model.rank left < model.rank right then
      Algo2Lean.UnionFind.link model left right else Algo2Lean.UnionFind.link model right left)
  by_cases same : left = right
  · simpa [unionHeap, Algo2Lean.UnionFind.union, left, right, same] using representation.tick "uf_union"
  · have valuesDifferent : (left.val : Int) ≠ (right.val : Int) := by
      intro eq; exact same (Fin.ext (by omega))
    by_cases less : model.rank left < model.rank right
    · have result := (representation.tick "uf_union").link left right same leftRoot rightRoot (by omega)
      have unequal : (model.rank left : Int) ≠ (model.rank right : Int) := by omega
      simpa [unionHeap, linkHeap, same,
        valuesDifferent, representation.ranks, less, unequal] using result
    · have result := (representation.tick "uf_union").link right left (Ne.symm same) rightRoot leftRoot (by omega)
      by_cases more : model.rank right < model.rank left
      · have unequal : (model.rank right : Int) ≠ (model.rank left : Int) := by omega
        simpa [unionHeap, linkHeap, same,
          valuesDifferent, representation.ranks, less, more, unequal] using result
      · have tied : model.rank left = model.rank right := by omega
        simpa [unionHeap, linkHeap, same,
          valuesDifferent, representation.ranks, less, more, tied] using result










/-- Lookup changes only the owned parent array. The larger footprint lets its
    contract compose directly with a later rank update. -/
theorem findHeap_frame (heap : Heap) (layout : Layout) (vertex root : Int) (length : Nat) :
    heap.Footprint (findHeap heap layout.parent vertex root length)
      [layout.parent, layout.rank] [] [] := by
  induction length generalizing heap vertex with
  | zero => exact (Heap.Footprint.refl heap _ _ _).tick "uf_find"
  | succ length ih =>
    exact (((Heap.Footprint.refl heap _ _ _).tick "uf_find").trans
      (ih (heap.tick "uf_find") (heap.read layout.parent vertex))).write
      layout.parent vertex root (Or.inl (by simp)) |>.tick "uf_compress"

theorem unionHeap_frame (heap : Heap) (layout : Layout) (left right : Int) :
    heap.Footprint (unionHeap heap layout left right) [layout.parent, layout.rank] [] [] := by
  have charged := (Heap.Footprint.refl heap [layout.parent,layout.rank] [] []).tick "uf_union"
  unfold unionHeap
  split
  · exact charged
  · split
    · exact charged.write layout.parent left right (Or.inl (by simp))
    · split
      · exact charged.write layout.parent right left (Or.inl (by simp))
      · exact (charged.write layout.parent right left (Or.inl (by simp))).write
          layout.rank left _ (Or.inl (by simp))










/-- The exact lookup heap preserves all allocation boundaries. -/
theorem findHeap_storage (heap : Heap) (layout : Layout) (vertex root : Int) (length : Nat) :
    Storage heap (findHeap heap layout.parent vertex root length) [layout.parent] := by
  refine ⟨?_, findHeap_nextRef _ _ _ _ _, findHeap_nextObject _ _ _ _ _, ?_⟩
  · induction length generalizing heap vertex with
    | zero => exact (Heap.Footprint.refl heap _ _ _).tick "uf_find"
    | succ length ih =>
      exact (((Heap.Footprint.refl heap _ _ _).tick "uf_find").trans
        (ih (heap.tick "uf_find") (heap.read layout.parent vertex))).write
        layout.parent vertex root (Or.inl (by simp)) |>.tick "uf_compress"
  · induction length generalizing heap vertex with
    | zero => rfl
    | succ length ih =>
      simpa only [findHeap, Heap.tick_nextCollection, Heap.write_nextCollection] using
        (ih (heap.tick "uf_find") (heap.read layout.parent vertex))



/-- No array, object, or typed collection is allocated by the rank-link stage. -/
theorem unionHeap_storage (heap : Heap) (layout : Layout) (left right : Int) :
    Storage heap (unionHeap heap layout left right) [layout.parent, layout.rank] := by
  refine ⟨unionHeap_frame _ _ _ _, ?_, ?_, ?_⟩ <;>
    by_cases same : left = right <;>
    by_cases less : heap.read layout.rank left < heap.read layout.rank right <;>
    by_cases more : heap.read layout.rank right < heap.read layout.rank left <;>
    simp [unionHeap, same, less, more]



/-- Union exposes the two actual compressed paths and the exact final model.
    Its caller can use a logarithmic or amortized bound on those paths while
    retaining the same operational Call, mutation footprint, and cost record. -/
theorem union_contract {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (a b : Fin n) :
    ∃ first second after,
      Find model a (model.representative a) first ∧
      Find (findResult model a first) b ((findResult model a first).representative b) second ∧
      UnionFind.union.Call heap (layout.object, (a.val : Int), (b.val : Int)) after
        (decide (model.representative a ≠ model.representative b)) ∧
      Rep after layout (unionResult model a b first second) ∧
      Storage heap after [layout.parent, layout.rank] ∧
      heap.Increments after (unionCosts first second) := by
  obtain ⟨first, firstPath⟩ := find_exists representation.valid a
  let middle := findHeap heap layout.parent a.val (model.representative a).val first
  let firstModel := findResult model a first
  have firstRep : Rep middle layout firstModel := findHeap_rep firstPath heap layout representation
  obtain ⟨second, secondPath⟩ := find_exists firstRep.valid b
  let linked := findHeap middle layout.parent b.val (firstModel.representative b).val second
  let secondModel := findResult firstModel b second
  have secondRep : Rep linked layout secondModel := findHeap_rep secondPath middle layout firstRep
  have representatives : secondModel.representative = model.representative := by
    simp [secondModel, firstModel]
  let after := unionHeap linked layout (secondModel.representative a).val (secondModel.representative b).val
  have firstCall := find_path first heap layout.object layout.parent _ _ representation.object
    representation.readParent representation.parentAllocated (model_path representation firstPath)
  have secondCall := find_path second middle layout.object layout.parent _ _ firstRep.object
    firstRep.readParent firstRep.parentAllocated (model_path firstRep secondPath)
  have sourceCall := union_calls heap middle linked layout a.val b.val
    (model.representative a).val (firstModel.representative b).val firstCall secondCall
    secondRep.readParent secondRep.readRank secondRep.parentAllocated secondRep.rankAllocated secondRep.separate
  refine ⟨first, second, after, firstPath, secondPath, ?_, unionHeap_rep secondRep a b, ?_, ?_⟩
  · simpa [after, representatives, firstModel, Int.ofNat_inj, Fin.val_inj] using sourceCall
  · have firstStorage := findHeap_storage heap layout a.val (model.representative a).val first
    have secondStorage := findHeap_storage middle layout b.val (firstModel.representative b).val second
    have lastStorage := unionHeap_storage linked layout (secondModel.representative a).val (secondModel.representative b).val
    refine ⟨(findHeap_frame heap layout _ _ first).trans
      ((findHeap_frame middle layout _ _ second).trans (unionHeap_frame linked layout _ _)), ?_, ?_, ?_⟩
    · exact lastStorage.nextRef.trans (secondStorage.nextRef.trans firstStorage.nextRef)
    · exact lastStorage.nextObject.trans (secondStorage.nextObject.trans firstStorage.nextObject)
    · exact lastStorage.nextCollection.trans (secondStorage.nextCollection.trans firstStorage.nextCollection)
  · intro clock
    simp only [after, unionHeap_clocks, linked, middle, findHeap_clocks, unionCosts, findCosts]
    omega
















-- Main result: Correctness and running time


end UnionFindAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} (heap : Algo2LeanGenerated.Heap) (layout : UnionFindAnalysis.Layout)
      (model : Algo2Lean.UnionFind.State n),
      UnionFindAnalysis.Rep heap layout model →
        ∀ (a b : Fin n),
          Exists.{1} fun first =>
            Exists.{1} fun second =>
              Exists.{1} fun after =>
                Algo2Lean.UnionFind.Find model a (model.representative a) first ∧
                  Algo2Lean.UnionFind.Find (UnionFindAnalysis.findResult model a first) b
                      ((UnionFindAnalysis.findResult model a first).representative b) second ∧
                    Algo.union_find.UnionFind.union.Call heap
                        (Prod.mk.{0, 0} layout.object
                          (Prod.mk.{0, 0} (↑(↑a : Nat) : Int) (↑(↑b : Nat) : Int)))
                        after
                        (Decidable.decide (Ne.{1} (model.representative a) (model.representative b))) ∧
                      UnionFindAnalysis.Rep after layout
                          (UnionFindAnalysis.unionResult model a b first second) ∧
                        UnionFindAnalysis.Storage heap after
                            (List.cons.{0} layout.parent (List.cons.{0} layout.rank List.nil.{0})) ∧
                          heap.Increments after (UnionFindAnalysis.unionCosts first second) :=
  UnionFindAnalysis.union_contract
