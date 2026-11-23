-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.matrix_decomp_lieAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:55.852396+00:00
-- url     : https://prove2.me/submissions/6ed882e6-b53e-4bef-b952-a2c8f023a3d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    M = (1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε) + Complex.I • ((-Complex.I / 2 : ℂ) • (M + Jm ε * Mᴴ * Jm ε)) := by
  rw [smul_smul, show Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; norm_num]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.DS
