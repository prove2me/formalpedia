-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.maDensity_gbPot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:20.153273+00:00
-- url     : https://prove2.me/submissions/9968c941-b051-4417-9b39-ebba666e87c7

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_det_cxHessian_gbPot
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_const


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
    maDensity (fun _ : Fin D => gbPot) y =
      (D.factorial : ℝ) / Real.pi ^ D * ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹ := by
  have hmd : mixedDisc (fun _ : Fin D => cxHessian gbPot y) = (cxHessian gbPot y).det :=
    ReciprocityTheory.AnForm.A.mdisc_const _
  simp only [maDensity, hmd, det_cxHessian_gbPot]
  have hG : (gbG y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gbG_pos y).ne'
  have : (1 / ((2 : ℂ) ^ D * (gbG y : ℂ) ^ (D + 1))) = ((1 / ((2 : ℝ) ^ D * (gbG y) ^ (D + 1)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.ofReal_re]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hGr : gbG y ≠ 0 := (gbG_pos y).ne'
  unfold gbG at hGr ⊢
  rw [div_pow]
  field_simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
