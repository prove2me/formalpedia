-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:51.06632+00:00
-- url     : https://prove2.me/submissions/993f0e43-9e41-476d-9350-f847dc55c792

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
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) : (polar_L g)ᴴ = polar_L g := by
  have h : IsSelfAdjoint (CFC.log (gᴴ * g)) := cfc_predicate Real.log (gᴴ * g)
  exact (IsSelfAdjoint.all (1 / 2 : ℝ)).smul h
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
