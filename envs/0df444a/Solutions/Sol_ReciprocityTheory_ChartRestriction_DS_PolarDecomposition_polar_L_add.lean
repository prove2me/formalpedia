-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:56.827565+00:00
-- url     : https://prove2.me/submissions/254613ca-beee-41f6-8796-4250f6418545

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose

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
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) :
    polar_L g + polar_L g = CFC.log (gᴴ * g) := by
  rw [polar_L, ← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
