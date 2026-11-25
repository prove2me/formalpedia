-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.stdBasis_reprV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:58.562608+00:00
-- url     : https://prove2.me/submissions/ba3b6ee9-bc11-434b-89ab-a03560a1bba9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {Q : Type} [Fintype Q] [DecidableEq Q] (x : Matrix (Fin n) Q ℂ) (i : Fin n) (j : Q) :
    (Matrix.stdBasis ℂ (Fin n) Q).repr x (i, j) = x i j := by
  first
    | rfl
    | (simp [Matrix.stdBasis]; done)
    | (simp [Matrix.stdBasis, Basis.reindex_repr, Pi.basis_repr]; done)
end ReciprocityTheory.ChartRestriction.DS.S7
