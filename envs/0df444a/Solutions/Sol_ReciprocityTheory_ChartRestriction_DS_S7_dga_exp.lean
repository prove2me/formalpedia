-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dga_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:47.507215+00:00
-- url     : https://prove2.me/submissions/46fa1564-7931-4adf-baaf-af2452ec47d0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • W)) W 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) W (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • W)) = fun u : ℝ => NormedSpace.exp (u • W) := by
    funext t
    rw [Complex.coe_smul]
  rw [e]
  exact h
end ReciprocityTheory.ChartRestriction.DS.S7
