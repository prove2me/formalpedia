-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_exp_Jconj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:30.108868+00:00
-- url     : https://prove2.me/submissions/4cbf5426-56ae-4755-9b79-39d55d6df1eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_J_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_Jinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
theorem _root_.solution (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Jm ε * A * Jm ε) = Jm ε * NormedSpace.exp A * Jm ε := by
  have h := Matrix.exp_conj (Jm ε) A (polar_J_unit ε)
  rwa [polar_Jinv] at h
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
