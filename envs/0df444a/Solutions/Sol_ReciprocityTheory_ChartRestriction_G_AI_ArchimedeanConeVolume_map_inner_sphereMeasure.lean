-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.map_inner_sphereMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:15.193379+00:00
-- url     : https://prove2.me/submissions/3f36b5e2-1f9c-4f90-ae38-2721d4f0315d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_volume_cone
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_cone_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_toSphere_univ_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_toSphere_univ_ne_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution {u : E3} (hu : ‖u‖ = 1) :
    sphereMeasure.map (fun n : S2 => inner ℝ (n : E3) u) =
      (2⁻¹ : ℝ≥0∞) • volume.restrict (Ioo (-1 : ℝ) 1) := by
  have hφ : Measurable (fun n : S2 => inner ℝ (n : E3) u) := by fun_prop
  set c := (volume : Measure E3).toSphere univ
  set K : ℝ≥0∞ := c⁻¹ * (Module.finrank ℝ E3 * coneConst)
  have key : ∀ s : Set ℝ, MeasurableSet s →
      sphereMeasure.map (fun n : S2 => inner ℝ (n : E3) u) s =
        K * volume.restrict (Ioo (-1 : ℝ) 1) s := by
    intro s hs
    rw [Measure.map_apply hφ hs, sphereMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.toSphere_apply' _ (hφ hs)]
    rw [show (fun n : S2 => inner ℝ (n : E3) u) ⁻¹' s = {n : S2 | inner ℝ (n : E3) u ∈ s} from rfl,
      cone_eq, volume_cone hu hs, Measure.restrict_apply hs]
    simp only [K, c]
    ring
  have hK : K = 2⁻¹ := by
    apply ENNReal.eq_inv_of_mul_eq_one_left
    have h1 := key univ MeasurableSet.univ
    rw [Measure.map_apply hφ MeasurableSet.univ, preimage_univ, sphereMeasure,
      Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel toSphere_univ_ne_zero
      toSphere_univ_ne_top, Measure.restrict_apply_univ, Real.volume_Ioo] at h1
    rw [h1]
    norm_num
  ext s hs
  rw [key s hs, hK, Measure.smul_apply, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
