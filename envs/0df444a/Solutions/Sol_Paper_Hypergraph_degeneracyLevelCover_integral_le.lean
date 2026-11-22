-- Prove2me | solution 1 for Paper.Hypergraph.degeneracyLevelCover_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:16.779846+00:00
-- url     : https://prove2.me/submissions/1d77b395-9eda-4184-af02-4d0fd3b740e4

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
import Theorems.Thm_Paper_Hypergraph_incidence_order_left_card
import Theorems.Thm_Paper_Hypergraph_vertexMultiplier_integrable
import Theorems.Thm_Paper_Hypergraph_vertexMultiplier_integral_le_one
import Theorems.Thm_Paper_Hypergraph_levelMeasure_Icc_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ} {x d y q : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hy : ∀ e ∈ H.edges, 0 ≤ y e)
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    {e : ℕ} (he : e ∈ H.edges) :
    ∫ r, H.degeneracyLevelCover rank x d y q e r ∂levelMeasure ≤ 6 * H.degeneracy * y e := by
  have hye := hy e he
  let L := (H.edge e).filter (fun v => rank (.inr e) < rank (.inl v))
  have hleft : (∫ r, ∑ v ∈ L, 2 * y e * vertexMultiplier x d v r ∂levelMeasure) ≤ 2 * H.degeneracy * y e := by
    rw [integral_finsetSum _ (fun v _ => (vertexMultiplier_integrable x d v).const_mul _)]
    have hcard : (L.card : ℝ) ≤ H.degeneracy := by exact_mod_cast H.incidence_order_left_card hlater he
    calc
      _ ≤ ∑ _v ∈ L, 2 * y e := sum_le_sum (fun v hv => by
        rw [integral_const_mul]
        exact (mul_le_mul_of_nonneg_left (vertexMultiplier_integral_le_one
          (hx v (H.edge_subset e he (mem_filter.mp hv).1))) (by positivity)).trans_eq (mul_one _))
      _ = (L.card : ℝ) * (2 * y e) := by simp
      _ ≤ _ := by nlinarith
  have hright : (∫ r, (Set.Icc (q e - 2 * H.degeneracy * y e) (q e + 2 * H.degeneracy * y e)).indicator
      (fun _ => (1 : ℝ)) r ∂levelMeasure) ≤ 4 * H.degeneracy * y e := by
    rw [integral_indicator_const _ measurableSet_Icc]
    simp only [smul_eq_mul, mul_one]
    apply (levelMeasure_Icc_le _ _).trans
    have hnonneg : (0 : ℝ) ≤ H.degeneracy * y e := mul_nonneg (Nat.cast_nonneg _) hye
    rw [max_eq_left (by nlinarith)]
    nlinarith
  simp only [degeneracyLevelCover]
  rw [integral_add
    (integrable_finsetSum _ (fun v _ => (vertexMultiplier_integrable x d v).const_mul _))
    ((integrable_const _).indicator measurableSet_Icc)]
  change (∫ r, ∑ v ∈ L, 2 * y e * vertexMultiplier x d v r ∂levelMeasure) + _ ≤ _
  linarith
end Paper.Hypergraph
