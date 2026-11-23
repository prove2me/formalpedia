-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exp_zero_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:48.916802+00:00
-- url     : https://prove2.me/submissions/663f7095-3850-4f42-bfa8-9545d1d02315

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InPApplyEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
end ReciprocityTheory.ChartRestriction.DS
