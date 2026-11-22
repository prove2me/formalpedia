-- Prove2me | solution 1 for Paper.Hypergraph.roundingThreshold_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:27.81554+00:00
-- url     : https://prove2.me/submissions/5c6e83f2-9c98-4f46-8ab6-3e4f2d4da957

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_coverCost_mono
import Theorems.Thm_Paper_Hypergraph_coverCost_smul


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {a : ℝ} (ha : 0 < a) :
    H.setCoverCost (H.roundingThreshold x a) ≤ a⁻¹ * H.coverCost x := by
  calc
    _ ≤ H.coverCost (a⁻¹ • x) := by
      apply H.coverCost_mono
      intro v hv
      simp only [indicator, Pi.smul_apply, smul_eq_mul]
      split_ifs with hm
      · have hax := (mem_filter.mp hm).2
        calc
          1 = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
          _ ≤ a⁻¹ * x v := mul_le_mul_of_nonneg_left hax (inv_nonneg.mpr ha.le)
      · exact mul_nonneg (inv_nonneg.mpr ha.le) (hx v hv)
    _ = _ := H.coverCost_smul x (inv_pos.mpr ha)
end Paper.Hypergraph
