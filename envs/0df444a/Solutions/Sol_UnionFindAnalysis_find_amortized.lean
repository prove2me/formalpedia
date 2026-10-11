-- Prove2me | solution 1 for UnionFindAnalysis.find_amortized
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:56:46.358287+00:00
-- url     : https://prove2.me/submissions/b19c315b-5fee-4e6f-87d8-ee863769911b

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_UnionFindAnalysis_find_contract
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Inverse-Ackermann amortized analysis for union by rank and full path compression.

The Ackermann hierarchy and its least positive inverse are defined and proved
in `Algo2LeanLib.Ackermann`. This module uses the rank/level/iteration potential
argument of Cormen, Leiserson, Rivest, and Stein, Introduction to Algorithms,
second edition, §21.4. All definitions and proofs below are independent of
compiled programs and their heap representation.

A positive-rank nonroot records the largest Ackermann level below its parent's
rank and the number of iterations reached within that level. Its credit is
`alpha(n) * rank - (level * rank + iterations)`; a root has `alpha(n) * rank`
credit. A rank-zero node has zero credit. The global potential sums these
nonnegative credits over the fixed universe.

Path compression increases a node's hierarchy progress whenever its old level
occurs again later on the path. All but at most one rank-zero node and one node
per level therefore pay for their own traversed edge. A rank link can increase
credit only at the winning root, by at most `alpha(n)`. Scaling the potential
by two pays for both the find and compression events in the source cost model.

The reusable local results are `find_amortized` and `union_amortized`.
`Operations.from_initial` telescopes their bounds across arbitrary finite
operation sequences; `Operations.total_cost` includes initialization and gives
`n + 1 + 13 * (finds + unions) * alpha(n)`. The logarithmic worst-case bound
for an individual operation remains available from `Algo2LeanLib.UnionFind`.
-/

namespace Algo2Lean.UnionFind





























open Algo2Lean.Ackermann

noncomputable section











































































/-- Scaling credits by two pays one root test plus both events on every nonroot step. -/
theorem find_amortized {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    (2 * steps + 1) + 2 * potential (compressPath state vertex steps) ≤
      2 * potential state + 2 * alpha n + 3 := by
  have charged := compressPath_amortized valid path
  omega







-- Main result: Running time




end
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


















open Algo2Lean.UnionFind (State Find compress    )



















































































/-- An actual lookup pays for its exact clock increments using the Ackermann
    potential. The resulting heap, partition model, and storage frame belong
    to the same call; no runtime assumption is supplied by the caller. -/
theorem find_amortized {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (vertex : Fin n) :
    ∃ after compressed,
      UnionFind.find.Call heap (layout.object, (vertex.val : Int)) after
        ((model.representative vertex).val : Int) ∧
      Rep after layout compressed ∧
      compressed.representative = model.representative ∧ compressed.rank = model.rank ∧
      Storage heap after [layout.parent] ∧
      heap.Increments after (Heap.cost heap after) ∧
      work (Heap.cost heap after) + 2 * Algo2Lean.UnionFind.potential compressed ≤
        2 * Algo2Lean.UnionFind.potential model + 2 * Algo2Lean.Ackermann.alpha n + 3 := by
  obtain ⟨length, after, path, execution, represented, storage, increments⟩ :=
    find_contract heap layout model representation vertex
  refine ⟨after, findResult model vertex length, execution, represented,
    findResult_representative _ _ _, findResult_rank _ _ _, storage,
    increments.monotone.increments, ?_⟩
  rw [increments.cost, work_findCosts]
  exact Algo2Lean.UnionFind.find_amortized representation.valid path



-- Main result: Correctness and running time


end UnionFindAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} (heap : Algo2LeanGenerated.Heap) (layout : UnionFindAnalysis.Layout)
      (model : Algo2Lean.UnionFind.State n),
      UnionFindAnalysis.Rep heap layout model →
        ∀ (vertex : Fin n),
          Exists.{1} fun after =>
            Exists.{1} fun compressed =>
              Algo.union_find.UnionFind.find.Call heap
                  (Prod.mk.{0, 0} layout.object (↑(↑vertex : Nat) : Int)) after
                  (↑(↑(model.representative vertex) : Nat) : Int) ∧
                UnionFindAnalysis.Rep after layout compressed ∧
                  Eq.{1} compressed.representative model.representative ∧
                    Eq.{1} compressed.rank model.rank ∧
                      UnionFindAnalysis.Storage heap after (List.cons.{0} layout.parent List.nil.{0}) ∧
                        heap.Increments after (heap.cost after) ∧
                          LE.le.{0}
                            (HAdd.hAdd.{0, 0, 0} (UnionFindAnalysis.work (heap.cost after))
                              (HMul.hMul.{0, 0, 0} (2 : Nat)
                                (Algo2Lean.UnionFind.potential compressed)))
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model))
                                (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.Ackermann.alpha n)))
                              (3 : Nat)) :=
  UnionFindAnalysis.find_amortized
