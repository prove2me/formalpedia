-- Prove2me | solution 1 for Paper.Hypergraph.regularized_width_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:18.733741+00:00
-- url     : https://prove2.me/submissions/56b73f06-25f6-491e-8c43-5089f3ad9608

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_regularized_main_width_comparison
import Theorems.Thm_Paper_Hypergraph_quantitative_reverse_comparison

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (rounding : BalancedRounding) :
    (∃ C : ℝ, 0 < C ∧ ∀ H : Hypergraph,
      H.fhw ≤ C * H.componentFactor * (H.adw + 1) * Real.log (2 + H.adw)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ H : Hypergraph,
      H.adw + 1 ≤ H.subw + 1 ∧
      c * (H.fhw / (H.componentFactor * Real.log (2 + H.fhw))) ≤ H.adw + 1) := by
  exact ⟨regularized_main_width_comparison rounding, quantitative_reverse_comparison rounding⟩
end Paper.Hypergraph
