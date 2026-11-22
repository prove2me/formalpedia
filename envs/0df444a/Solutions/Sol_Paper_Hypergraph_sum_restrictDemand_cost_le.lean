-- Prove2me | solution 1 for Paper.Hypergraph.sum_restrictDemand_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:29.200979+00:00
-- url     : https://prove2.me/submissions/dc93646f-33ec-4164-bcba-f41a1a264ddb

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_le_coverCost


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (P : ι → Finset ℕ) (x : ℕ → ℝ)
    (hsep : ∀ e ∈ H.edges, ∀ i ∈ I, ∀ j ∈ I,
      ¬ Disjoint (H.edge e) (P i) → ¬ Disjoint (H.edge e) (P j) → i = j) :
    (∑ i ∈ I, H.coverCost (restrictDemand x (P i))) ≤ H.coverCost x := by
  classical
  apply H.le_coverCost
  intro y hy
  let z : ι → ℕ → ℝ := fun i e => if ¬ Disjoint (H.edge e) (P i) then y e else 0
  have hz : ∀ i, H.Cover (restrictDemand x (P i)) (z i) := by
    intro i
    constructor
    · intro e he
      dsimp [z]
      split_ifs <;> first | exact hy.1 e he | exact le_rfl
    · intro v hv
      by_cases hvi : v ∈ P i
      · have heq : (∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), z i e) =
            ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e := by
          apply sum_congr rfl
          intro e he
          have hm : ¬ Disjoint (H.edge e) (P i) :=
            not_disjoint_iff.mpr ⟨v, (mem_filter.mp he).2, hvi⟩
          simp [z, hm]
        simpa [restrictDemand, hvi, heq] using hy.2 v hv
      · simp only [restrictDemand, if_neg hvi]
        apply sum_nonneg
        intro e he
        dsimp [z]
        split_ifs <;> first | exact hy.1 e (mem_filter.mp he).1 | exact le_rfl
  calc
    _ ≤ ∑ i ∈ I, ∑ e ∈ H.edges, z i e := sum_le_sum fun i _ => H.coverCost_le (hz i)
    _ = ∑ e ∈ H.edges, ∑ i ∈ I, z i e := sum_comm
    _ ≤ ∑ e ∈ H.edges, y e := by
      apply sum_le_sum
      intro e he
      by_cases hm : ∃ i ∈ I, ¬ Disjoint (H.edge e) (P i)
      · obtain ⟨i, hi, hmi⟩ := hm
        have hs : (∑ j ∈ I, z j e) = z i e := by
          apply sum_eq_single i
          · intro j hj hji
            have hd : Disjoint (H.edge e) (P j) := by
              by_contra hnd
              exact hji (hsep e he j hj i hi hnd hmi)
            simp [z, hd]
          · exact fun h => (h hi).elim
        rw [hs]
        simp [z, hmi]
      · have hz0 : ∀ i ∈ I, z i e = 0 := by
          intro i hi
          have hd : Disjoint (H.edge e) (P i) := by
            by_contra hnd
            exact hm ⟨i, hi, hnd⟩
          simp [z, hd]
        rw [sum_eq_zero hz0]
        exact hy.1 e he
end Paper.Hypergraph
