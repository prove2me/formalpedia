-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_lintegral_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:53.05397+00:00
-- url     : https://prove2.me/submissions/b27cee7e-4e0d-4c11-876d-f5a5cb775449

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_integrableOn_Ioi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_integral_Ioi

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
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {b : ℝ} (hb : 0 < b) (j : ℕ) :
    ∫⁻ t : ℂ, ENNReal.ofReal (((b + ‖t‖ ^ 2) ^ (j + 2))⁻¹) =
      ENNReal.ofReal (Real.pi / (((j : ℝ) + 1) * b ^ (j + 1))) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hcongr : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      ENNReal.ofReal (((b + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (j + 2))⁻¹) =
      ENNReal.ofReal (p.1 * ((b + p.1 ^ 2) ^ (j + 2))⁻¹) * 1 := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp1, smul_eq_mul, mul_one,
      ENNReal.ofReal_mul hp1.le]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hcongr]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((b + r ^ 2) ^ (j + 2))⁻¹))
    (g := fun _ : ℝ => (1 : ℝ≥0∞)) (by fun_prop) aemeasurable_const]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaM_integrableOn_Ioi hb j)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
      have : 0 < b + x ^ 2 := by positivity
      exact mul_nonneg (le_of_lt hx) (by positivity))]
  rw [gaM_integral_Ioi hb j, setLIntegral_one, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : (0 : ℝ) < b ^ (j + 1) := by positivity
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
