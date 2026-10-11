-- Prove2me | solution 1 for UnionFindAnalysis.find_contract
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:51.915979+00:00
-- url     : https://prove2.me/submissions/feb9a97c-fe62-4799-8bde-4af90da77765

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid


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

/-- Lookup costs are increments from the caller's actual counters. -/
theorem findHeap_increments (heap : Heap) (parent : SeqRef) (vertex root : Int) (length : Nat) :
    heap.Increments (findHeap heap parent vertex root length) (findCosts length) := by
  intro clock
  simp [findCosts, findHeap_clocks, Nat.add_assoc]



/-- A lookup has a finite path witness, the exact fully compressed model, a
    parent-only storage footprint, unchanged allocation boundaries, and exact
    clock increments. This contract supports later potential arguments without
    reopening the compiled transitions. -/
theorem find_contract {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (vertex : Fin n) :
    ∃ length after,
      Find model vertex (model.representative vertex) length ∧
      UnionFind.find.Call heap (layout.object, (vertex.val : Int)) after
        ((model.representative vertex).val : Int) ∧
      Rep after layout (findResult model vertex length) ∧
      Storage heap after [layout.parent] ∧
      heap.Increments after (findCosts length) := by
  obtain ⟨length, path⟩ := find_exists representation.valid vertex
  refine ⟨length, findHeap heap layout.parent vertex.val (model.representative vertex).val length,
    path, ?_, findHeap_rep path heap layout representation,
    findHeap_storage _ _ _ _ _, findHeap_increments _ _ _ _ _⟩
  exact find_path length heap layout.object layout.parent _ _ representation.object
    representation.readParent representation.parentAllocated (model_path representation path)


















-- Main result: Correctness and running time


end UnionFindAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} (heap : Algo2LeanGenerated.Heap) (layout : UnionFindAnalysis.Layout)
      (model : Algo2Lean.UnionFind.State n),
      UnionFindAnalysis.Rep heap layout model →
        ∀ (vertex : Fin n),
          Exists.{1} fun length =>
            Exists.{1} fun after =>
              Algo2Lean.UnionFind.Find model vertex (model.representative vertex) length ∧
                Algo.union_find.UnionFind.find.Call heap
                    (Prod.mk.{0, 0} layout.object (↑(↑vertex : Nat) : Int)) after
                    (↑(↑(model.representative vertex) : Nat) : Int) ∧
                  UnionFindAnalysis.Rep after layout
                      (UnionFindAnalysis.findResult model vertex length) ∧
                    UnionFindAnalysis.Storage heap after (List.cons.{0} layout.parent List.nil.{0}) ∧
                      heap.Increments after (UnionFindAnalysis.findCosts length) :=
  UnionFindAnalysis.find_contract
