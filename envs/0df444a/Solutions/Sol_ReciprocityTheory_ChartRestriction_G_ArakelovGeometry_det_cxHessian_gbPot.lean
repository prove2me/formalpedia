-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.det_cxHessian_gbPot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:26.986927+00:00
-- url     : https://prove2.me/submissions/cd08e562-98ec-4be6-b150-ae86087ecec7

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_cxHessian_gbPot_eq

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
    (cxHessian gbPot y).det = 1 / ((2 : ℂ) ^ D * (gbG y : ℂ) ^ (D + 1)) := by
  have hG : (gbG y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gbG_pos y).ne'
  rw [cxHessian_gbPot_eq, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : ∑ i, y i * starRingEnd ℂ (y i) = ((gbG y - 1 : ℝ) : ℂ) := by
    rw [gbG, add_sub_cancel_left, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdot : y ⬝ᵥ (fun i => -(starRingEnd ℂ (y i)) / (gbG y : ℂ)) =
      -(∑ i, y i * starRingEnd ℂ (y i)) / (gbG y : ℂ) := by
    simp only [dotProduct, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdot, hs, Fintype.card_fin]
  push_cast
  simp only [inv_pow, one_div_pow, one_div]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
