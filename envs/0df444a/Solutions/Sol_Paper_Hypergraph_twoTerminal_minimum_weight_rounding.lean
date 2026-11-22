-- Prove2me | solution 1 for Paper.Hypergraph.twoTerminal_minimum_weight_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:55.481578+00:00
-- url     : https://prove2.me/submissions/1f5e9245-5b38-4302-8cf6-fc05c0df5957

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging
import Theorems.Thm_Paper_Hypergraph_intervalMultiplier_measurable
import Theorems.Thm_Paper_Hypergraph_intervalMultiplier_nonneg
import Theorems.Thm_Paper_Hypergraph_intervalMultiplier_le
import Theorems.Thm_Paper_Hypergraph_intervalMultiplier_integral_le
import Theorems.Thm_Paper_Hypergraph_rounding_by_average
import Theorems.Thm_Paper_Hypergraph_coverCost_attained
import Theorems.Thm_Paper_Hypergraph_edge_intervals_common_point
import Theorems.Thm_Paper_Hypergraph_twoTerminal_distance_labels


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices) (hx : H.FractionalSeparator A B x)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : ∀ v ∈ H.vertices, x v = 0 ∨ ε ≤ x v) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ (1 + 2 * Real.log (1 / ε)) * H.coverCost x := by
  obtain ⟨d, hd, ha, hb, hstep⟩ := H.twoTerminal_distance_labels hA hx
  obtain ⟨y, hy, _, hcost⟩ := H.coverCost_attained hx.1
  let m : ℕ → ℝ → ℝ := fun e r => if he : e ∈ H.edges then
    intervalMultiplier (H.edge e) (H.edge_nonempty e he) x d r * y e else 0
  have hmult_i (e : ℕ) (he : e ∈ H.edges) :
      Integrable (intervalMultiplier (H.edge e) (H.edge_nonempty e he) x d) levelMeasure := by
    apply (integrable_const (1 / ε)).mono'
      (intervalMultiplier_measurable _ _ _ _).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalMultiplier_nonneg _
      (fun v hv => (hx.1 v (H.edge_subset e he hv)).1) r)]
    exact intervalMultiplier_le _ hε (fun v hv => hsmall v (H.edge_subset e he hv)) r
  have hi : ∀ e ∈ H.edges, Integrable (m e) levelMeasure := by
    intro e he
    simpa [m, he] using (hmult_i e he).mul_const (y e)
  obtain ⟨S, hS, hsep, hbound⟩ := H.rounding_by_average hA hB ha hb hstep m hi (by
    intro r hr
    have hm0 : ∀ e ∈ H.edges, 0 ≤ m e r := by
      intro e he
      simp only [m, dif_pos he]
      exact mul_nonneg (intervalMultiplier_nonneg _
        (fun v hv => (hx.1 v (H.edge_subset e he hv)).1) r) (hy.1 e he)
    refine ⟨hm0, ?_⟩
    intro v hv
    by_cases hvS : v ∈ H.levelSeparator x d r
    swap
    · simp only [indicator, if_neg hvS]
      exact Finset.sum_nonneg (fun e he => hm0 e (Finset.mem_filter.mp he).1)
    have hvsel := (Finset.mem_filter.mp hvS).2
    have hxv : 0 < x v := lt_of_le_of_ne (hx.1 v hv).1 hvsel.1.symm
    have hmul : 1 ≤ (1 / x v) * ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e := by
      have h := mul_le_mul_of_nonneg_left (hy.2 v hv) (by positivity : 0 ≤ 1 / x v)
      simpa [ne_of_gt hxv] using h
    simp only [indicator, if_pos hvS]
    apply hmul.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨he, hve⟩ := Finset.mem_filter.mp he
    simp only [m, dif_pos he]
    apply mul_le_mul_of_nonneg_right _ (hy.1 e he)
    have h := Finset.le_sup' (fun w => vertexMultiplier x d w r) hve
    change 1 / x v ≤ (H.edge e).sup' _ (fun w => vertexMultiplier x d w r)
    have heq : vertexMultiplier x d v r = 1 / x v :=
      Set.indicator_of_mem (show r ∈ Icc (d v - x v) (d v) from hvsel.2) _
    rwa [heq] at h)
  refine ⟨S, hS, hsep, hbound.trans ?_⟩
  rw [hcost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨q, hq⟩ := H.edge_intervals_common_point hstep (fun v hv => (hx.1 v hv).1) he
  simp only [m, dif_pos he, integral_mul_const]
  exact mul_le_mul_of_nonneg_right (intervalMultiplier_integral_le _ hε hε1
    (fun v hv => hsmall v (H.edge_subset e he hv)) hq) (hy.1 e he)
end Paper.Hypergraph
