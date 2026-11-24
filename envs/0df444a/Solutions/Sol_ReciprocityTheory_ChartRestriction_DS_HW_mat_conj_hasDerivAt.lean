-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.mat_conj_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:58:43.364161+00:00
-- url     : https://prove2.me/submissions/479548ef-e3ef-4998-b1a1-62614cf15fcc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun z : ℂ => NormedSpace.exp (z • X) * Y * NormedSpace.exp (z • (-X)))
      (X * Y - Y * X) ((0 : ℝ) : ℂ) := by
  have := ((hasDerivAt_exp_smul_const X ((0 : ℝ) : ℂ)).mul_const Y).mul
    (hasDerivAt_exp_smul_const (-X) ((0 : ℝ) : ℂ))
  refine HasDerivAt.congr_deriv this ?_
  simp [sub_eq_add_neg]
end ReciprocityTheory.ChartRestriction.DS.HW
