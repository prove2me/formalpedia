-- Prove2me | solution 1 for UnionFindAnalysis.union_amortized
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:00:52.572886+00:00
-- url     : https://prove2.me/submissions/e8f01b71-42ed-4a21-88dd-34a4eeac515e

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_UnionFindAnalysis_union_contract
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_potential
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized


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































































theorem mergeRepresentative_eq_iff {n : Nat} (representative : Fin n → Fin n)
    (loser winner first second : Fin n) :
    mergeRepresentative representative loser winner first =
        mergeRepresentative representative loser winner second ↔
      representative first = representative second ∨
      (representative first = loser ∧ representative second = winner) ∨
      (representative first = winner ∧ representative second = loser) := by
  by_cases firstLoser : representative first = loser <;>
    by_cases secondLoser : representative second = loser
  · simp [mergeRepresentative, firstLoser, secondLoser]
  · simp [mergeRepresentative, firstLoser, secondLoser, Ne.symm secondLoser, eq_comm]
  · simp [mergeRepresentative, firstLoser, secondLoser, eq_comm]
  · simp [mergeRepresentative, firstLoser, secondLoser]

/-- A root link joins exactly its two former components. -/
theorem link_connected {n : Nat} {state : State n} (valid : Valid state)
    (loser winner : Fin n) (loserRoot : state.parent loser = loser)
    (winnerRoot : state.parent winner = winner) (first second : Fin n) :
    Connected (link state loser winner) first second ↔
      Connected state first second ∨
      (Connected state first loser ∧ Connected state second winner) ∨
      (Connected state first winner ∧ Connected state second loser) := by
  simpa only [Connected, link, valid.root_representative loser loserRoot,
    valid.root_representative winner winnerRoot] using
    mergeRepresentative_eq_iff state.representative loser winner first second





/-- Union's precise partition contract, independent of root selection and ranks. -/
theorem union_connected {n : Nat} {state : State n} (valid : Valid state)
    (first second a b : Fin n) :
    Connected (union state first second) a b ↔
      Connected state a b ∨
      (Connected state a first ∧ Connected state b second) ∨
      (Connected state a second ∧ Connected state b first) := by
  have firstRoot := valid.representative_root first
  have secondRoot := valid.representative_root second
  have firstRep := valid.root_representative _ firstRoot
  have secondRep := valid.root_representative _ secondRoot
  simp only [union]
  split
  · rename_i same
    simp only [Connected, same]
    constructor
    · exact Or.inl
    · intro joined
      rcases joined with old | joined | joined
      · exact old
      · exact joined.1.trans joined.2.symm
      · exact joined.1.trans joined.2.symm
  · split
    · simpa only [Connected, firstRep, secondRep] using
        link_connected valid _ _ firstRoot secondRoot a b
    · have joined := link_connected valid _ _ secondRoot firstRoot a b
      simp only [Connected, firstRep, secondRep] at joined ⊢
      constructor
      · intro connected
        rcases joined.mp connected with old | cross | cross
        · exact Or.inl old
        · exact Or.inr (Or.inr cross)
        · exact Or.inr (Or.inl cross)
      · intro connected
        apply joined.mpr
        rcases connected with old | cross | cross
        · exact Or.inl old
        · exact Or.inr (Or.inr cross)
        · exact Or.inr (Or.inl cross)





end Algo2Lean.UnionFind

end

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









/-- The structural invariant is preserved by every finite sequence of compression writes. -/
theorem compressPath_valid {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) (steps : Nat) : Valid (compressPath state vertex steps) := by
  induction steps generalizing vertex with
  | zero => exact valid
  | succ steps ih => exact compress_valid (ih (state.parent vertex)) vertex



















open Algo2Lean.Ackermann

noncomputable section





















































/-- Choosing the rank-ordered orientation does not affect the alpha-sized link budget. -/
theorem union_potential {n : Nat} {state : State n} (valid : Valid state) (first second : Fin n) :
    potential (union state first second) ≤ potential state + alpha n := by
  simp only [union]
  split
  · omega
  · rename_i different
    split
    · rename_i ordered
      exact link_potential valid _ _ different (valid.representative_root first)
        (valid.representative_root second) (by omega)
    · rename_i ordered
      exact link_potential valid _ _ (Ne.symm different) (valid.representative_root second)
        (valid.representative_root first) (by omega)





















/-- Scaling credits by two pays one root test plus both events on every nonroot step. -/
theorem find_amortized {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    (2 * steps + 1) + 2 * potential (compressPath state vertex steps) ≤
      2 * potential state + 2 * alpha n + 3 := by
  have charged := compressPath_amortized valid path
  omega

/-- Two compressed finds followed by a rank link have inverse-Ackermann amortized cost. -/
theorem union_amortized {n : Nat} {state : State n} (valid : Valid state)
    {first second firstRoot secondRoot : Fin n} {firstSteps secondSteps : Nat}
    (firstPath : Find state first firstRoot firstSteps)
    (secondPath : Find (compressPath state first firstSteps) second secondRoot secondSteps) :
    (2 * (firstSteps + secondSteps) + 3) +
        2 * potential (union (compressPath (compressPath state first firstSteps) second secondSteps) first second) ≤
      2 * potential state + 6 * alpha n + 7 := by
  have firstBudget := find_amortized valid firstPath
  have middleValid := compressPath_valid valid first firstSteps
  have secondBudget := find_amortized middleValid secondPath
  have finalValid := compressPath_valid middleValid second secondSteps
  have linkBudget := union_potential finalValid first second
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


















open Algo2Lean.UnionFind (State Find compress compress_valid   )













theorem findResult_valid {n : Nat} (model : State n) (vertex : Fin n)
    (length : Nat) (valid : Algo2Lean.UnionFind.Valid model) :
    Algo2Lean.UnionFind.Valid (findResult model vertex length) := by
  induction length generalizing vertex with
  | zero => exact valid
  | succ length ih => exact compress_valid (ih (model.parent vertex)) vertex
































































/-- The exact full-compression result represents the same partition. -/
theorem unionResult_connected {n : Nat} {model : State n}
    (valid : Algo2Lean.UnionFind.Valid model) (a b : Fin n) (first second : Nat) (x y : Fin n) :
    Algo2Lean.UnionFind.Connected (unionResult model a b first second) x y ↔
      Algo2Lean.UnionFind.Connected model x y ∨
      (Algo2Lean.UnionFind.Connected model x a ∧ Algo2Lean.UnionFind.Connected model y b) ∨
      (Algo2Lean.UnionFind.Connected model x b ∧ Algo2Lean.UnionFind.Connected model y a) := by
  have compressedValid := findResult_valid (findResult model a first) b second
    (findResult_valid model a first valid)
  simpa [unionResult, Algo2Lean.UnionFind.Connected] using
    Algo2Lean.UnionFind.union_connected compressedValid a b x y








-- Main result: Correctness and running time
/-- Union's full client contract exposes its precise partition effect, no
    allocation, storage preservation, actual cost increments, and an amortized
    budget that telescopes when the returned model is passed to the next call. -/
theorem union_amortized {n : Nat} (heap : Heap) (layout : Layout) (model : State n)
    (representation : Rep heap layout model) (a b : Fin n) :
    ∃ after nextModel,
      UnionFind.union.Call heap (layout.object, (a.val : Int), (b.val : Int)) after
        (decide (model.representative a ≠ model.representative b)) ∧
      Rep after layout nextModel ∧
      (∀ x y, Algo2Lean.UnionFind.Connected nextModel x y ↔
        Algo2Lean.UnionFind.Connected model x y ∨
        (Algo2Lean.UnionFind.Connected model x a ∧ Algo2Lean.UnionFind.Connected model y b) ∨
        (Algo2Lean.UnionFind.Connected model x b ∧ Algo2Lean.UnionFind.Connected model y a)) ∧
      Storage heap after [layout.parent, layout.rank] ∧
      heap.Increments after (Heap.cost heap after) ∧
      work (Heap.cost heap after) + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        2 * Algo2Lean.UnionFind.potential model + 6 * Algo2Lean.Ackermann.alpha n + 7 := by
  obtain ⟨first, second, after, firstPath, secondPath, execution, represented, storage, increments⟩ :=
    union_contract heap layout model representation a b
  refine ⟨after, unionResult model a b first second, execution, represented,
    unionResult_connected representation.valid a b first second, storage,
    increments.monotone.increments, ?_⟩
  rw [increments.cost, work_unionCosts]
  exact Algo2Lean.UnionFind.union_amortized representation.valid firstPath secondPath

end UnionFindAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} (heap : Algo2LeanGenerated.Heap) (layout : UnionFindAnalysis.Layout)
      (model : Algo2Lean.UnionFind.State n),
      UnionFindAnalysis.Rep heap layout model →
        ∀ (a b : Fin n),
          Exists.{1} fun after =>
            Exists.{1} fun nextModel =>
              Algo.union_find.UnionFind.union.Call heap
                  (Prod.mk.{0, 0} layout.object
                    (Prod.mk.{0, 0} (↑(↑a : Nat) : Int) (↑(↑b : Nat) : Int)))
                  after (Decidable.decide (Ne.{1} (model.representative a) (model.representative b))) ∧
                UnionFindAnalysis.Rep after layout nextModel ∧
                  (∀ (x y : Fin n),
                      Algo2Lean.UnionFind.Connected nextModel x y ↔
                        Algo2Lean.UnionFind.Connected model x y ∨
                          Algo2Lean.UnionFind.Connected model x a ∧
                              Algo2Lean.UnionFind.Connected model y b ∨
                            Algo2Lean.UnionFind.Connected model x b ∧
                              Algo2Lean.UnionFind.Connected model y a) ∧
                    UnionFindAnalysis.Storage heap after
                        (List.cons.{0} layout.parent (List.cons.{0} layout.rank List.nil.{0})) ∧
                      heap.Increments after (heap.cost after) ∧
                        LE.le.{0}
                          (HAdd.hAdd.{0, 0, 0} (UnionFindAnalysis.work (heap.cost after))
                            (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential nextModel)))
                          (HAdd.hAdd.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model))
                              (HMul.hMul.{0, 0, 0} (6 : Nat) (Algo2Lean.Ackermann.alpha n)))
                            (7 : Nat)) :=
  UnionFindAnalysis.union_amortized
