-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_radial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:34.253501+00:00
-- url     : https://prove2.me/submissions/fdde407b-22cd-46f5-8368-ae211cd14785

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PlanarKernelBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
theorem _root_.solution (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, g ‖x‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 • g ‖Complex.polarCoord.symm p‖ =
        (fun r : ℝ => ENNReal.ofReal r * g r) p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
    intro p hp
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul, mul_one]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) h1,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal r * g r) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      ((ENNReal.measurable_ofReal.mul hg).aemeasurable) aemeasurable_const]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, one_mul]
  rw [show π - -π = 2 * π by ring, mul_comm]
end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
