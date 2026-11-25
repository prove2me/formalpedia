-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.cxHessian_gbPot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:40.220603+00:00
-- url     : https://prove2.me/submissions/c257d450-ee87-4d00-9b9b-d3cca42829d2

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_fderiv_fderiv_gbPot_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbBil_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gb_I_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gb_conj_mul

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
theorem _root_.solution (y : Fin D → ℂ) (i j : Fin D) :
    cxHessian gbPot y i j =
      (((gbG y : ℂ) * (if i = j then 1 else 0) - starRingEnd ℂ (y i) * y j) / (2 * (gbG y : ℂ) ^ 2)) := by
  have hG : (gbG y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gbG_pos y).ne'
  simp only [cxHessian, fderiv_fderiv_gbPot_apply, gb_I_single, gbBil_single, gb_conj_mul]
  by_cases h : i = j
  · subst h
    simp only [Pi.single_apply, if_true, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    field_simp
    ring
  · simp only [Pi.single_apply, h, Ne.symm h, if_false, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    field_simp
    ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
