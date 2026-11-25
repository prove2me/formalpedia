-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.lint_scl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:47.7733+00:00
-- url     : https://prove2.me/submissions/3c66d3d1-8764-4599-81c9-22a63656e623

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_det_sclL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p m : ℕ} {G : Xp p m → ℝ≥0∞} (hG : Measurable G) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, G x = ENNReal.ofReal (t ^ (4 * p + 2 * m + 2)) * ∫⁻ x, G (sclL p m t x) := by
  have hdet : LinearMap.det (sclL p m t) ≠ 0 := by
    rw [det_sclL]
    exact pow_ne_zero _ ht.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Xp p m)) hdet
  have htp : 0 < t ^ (4 * p + 2 * m + 2) := pow_pos ht _
  rw [← MeasureTheory.lintegral_map hG (LinearMap.continuous_of_finiteDimensional (sclL p m t)).measurable, hmap,
    MeasureTheory.lintegral_smul_measure, det_sclL, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul htp.le,
    abs_of_pos (inv_pos.mpr htp), mul_inv_cancel₀ htp.ne', ENNReal.ofReal_one, one_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
