-- Prove2me | solution 1 for Paper.Hypergraph.rounding_by_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:37.759554+00:00
-- url     : https://prove2.me/submissions/6eef6cf6-930c-4524-81b3-e6268f4e0358

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging
import Theorems.Thm_Paper_Hypergraph_levelSeparator_integral
import Theorems.Thm_Paper_Hypergraph_levelSeparator_subset_support


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x d : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices)
    (ha : ∀ v ∈ A, d v ≤ x v) (hb : ∀ v ∈ B, 1 ≤ d v)
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    (m : ℕ → ℝ → ℝ) (hi : ∀ e ∈ H.edges, Integrable (m e) levelMeasure)
    (hc : ∀ r ∈ Ioo 0 1, H.Cover (indicator (H.levelSeparator x d r)) (fun e => m e r)) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ ∑ e ∈ H.edges, ∫ r, m e r ∂levelMeasure := by
  have hsum : Integrable (fun r => ∑ e ∈ H.edges, m e r) levelMeasure := integrable_finsetSum _ hi
  have hnull : levelMeasure (Ioo (0 : ℝ) 1)ᶜ = 0 := by simp [levelMeasure]
  obtain ⟨r, hr, hcost⟩ := exists_notMem_null_le_integral hsum hnull
  have hr' : r ∈ Ioo (0 : ℝ) 1 := by simpa using hr
  refine ⟨H.levelSeparator x d r, H.levelSeparator_subset_support x d r,
    H.levelSeparator_integral hA hB ha hb hstep hr', ?_⟩
  apply (H.coverCost_le (hc r hr')).trans
  rwa [integral_finsetSum _ hi] at hcost
end Paper.Hypergraph
