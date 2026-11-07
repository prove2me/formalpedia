-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_disjointUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:32.703111+00:00
-- url     : https://prove2.me/submissions/d93a448d-bacc-47b8-92e5-c4fe7aa1edaf

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (M : I → WeightedGraph V) (S T : Finset (I × V)) :
    crossCount (disjointUnion M) S T =
      ∑ i, crossCount (M i) (productFiber S i) (productFiber T i) := by
  classical
  simp only [crossCount, disjointUnion]
  rw [← Finset.sum_fiberwise S Prod.fst (fun iv =>
    ∑ ju ∈ T, if iv.1 = ju.1 then M iv.1 iv.2 ju.2 else 0)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [productFiber, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro iv hiv
    have hivFirst : iv.1 = i := (Finset.mem_filter.mp hiv).2
    calc
      (∑ ju ∈ T, if iv.1 = ju.1 then M iv.1 iv.2 ju.2 else 0) =
          ∑ ju ∈ T with ju.1 = i, M i iv.2 ju.2 := by
        simp only [hivFirst]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ju _hju
        by_cases hji : i = ju.1 <;> simp [hji, eq_comm]
      _ = ∑ u ∈ (T.filter fun ju => ju.1 = i).image Prod.snd,
          M i iv.2 u := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
          (Finset.mem_filter.mp hy).2.symm) hxy
  · intro x hx y hy hxy
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm) hxy
end QEC.Coding.SmallSetExpansion
