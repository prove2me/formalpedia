-- Prove2me | solution 1 for Paper.Hypergraph.degeneracyLevelCover_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:26.813635+00:00
-- url     : https://prove2.me/submissions/d74604c3-d0a4-4cb7-a11e-ee9a9c50af26

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
import Theorems.Thm_Paper_Hypergraph_vertexMultiplier_integrable

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (rank : ℕ ⊕ ℕ → ℕ) (x d y q : ℕ → ℝ)
    (e : ℕ) : Integrable (H.degeneracyLevelCover rank x d y q e) levelMeasure := by
  apply Integrable.add
  · exact integrable_finsetSum _ (fun v _ => (vertexMultiplier_integrable x d v).const_mul _)
  · exact (integrable_const _).indicator measurableSet_Icc
end Paper.Hypergraph
