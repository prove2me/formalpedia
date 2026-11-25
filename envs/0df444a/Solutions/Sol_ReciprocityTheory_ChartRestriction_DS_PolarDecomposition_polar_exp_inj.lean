-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_exp_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:50.751904+00:00
-- url     : https://prove2.me/submissions/b497b6e1-a070-49db-ae42-b378ae417999

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_sa

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
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  rw [← CFC.log_exp A (polar_sa hA), ← CFC.log_exp B (polar_sa hB), h]
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
