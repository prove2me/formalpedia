-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.cxHessian_gbPot_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:30.77353+00:00
-- url     : https://prove2.me/submissions/f5643b81-0eef-437f-bccc-67d7eac7b79b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbG_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_cxHessian_gbPot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MeasureTheory Set Filter Topology
open scoped ENNReal
open ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (y : Fin D → ℂ) :
    cxHessian gbPot y = (1 / (2 * (gbG y : ℂ))) •
      (1 + Matrix.replicateCol Unit (fun i => -(starRingEnd ℂ (y i)) / (gbG y : ℂ)) *
        Matrix.replicateRow Unit y) := by
  have hG : (gbG y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gbG_pos y).ne'
  ext i j
  rw [cxHessian_gbPot]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply, smul_eq_mul]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
