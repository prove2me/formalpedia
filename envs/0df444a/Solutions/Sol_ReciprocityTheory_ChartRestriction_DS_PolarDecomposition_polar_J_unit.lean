-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_J_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:47.406491+00:00
-- url     : https://prove2.me/submissions/1d0203ac-dfd3-4081-a359-360ee1892616

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_Jm_mul_self

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
theorem _root_.solution (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, polar_Jm_mul_self ε, polar_Jm_mul_self ε⟩, rfl⟩
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
