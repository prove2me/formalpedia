-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dga_path
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:46.022003+00:00
-- url     : https://prove2.me/submissions/ef853a01-3b6f-4ca5-bb4a-bb3b03ce4506

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dga_exp

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
theorem _root_.solution (Y z : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y)) * z * NormedSpace.exp ((t : ℂ) • Y))
      (z * Y - Y * z) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))) (-Y) 0 := by
    have h := dga_exp (-Y)
    simpa [smul_neg] using h
  have h2 := dga_exp Y
  have e0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  have e1 : NormedSpace.exp (-(((0 : ℝ) : ℂ) • Y)) = 1 := by simp
  have h3 := (h1.mul_const z).mul h2
  simp only [e0, e1, mul_one, one_mul] at h3
  have e2 : -Y * z + z * Y = z * Y - Y * z := by noncomm_ring
  rw [e2] at h3
  exact h3
end ReciprocityTheory.ChartRestriction.DS.S7
