-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:50.334829+00:00
-- url     : https://prove2.me/submissions/3f79aa5e-6adb-4d18-8c4f-4568df8e4c64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (a b : Fin n) :
    ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 + (c * v 0) • A) a b := by
  have h0 : ContDiff ℝ 2 fun v : Fin 1 → ℂ => v 0 := contDiff_pi.mp contDiff_id 0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.add ((contDiff_const.mul h0).mul contDiff_const)
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
