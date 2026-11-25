-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_sq_lintegral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:36.728919+00:00
-- url     : https://prove2.me/submissions/3185a9c8-66af-424a-872f-4c8d93a3d2fa

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {f : ℝ → ENNReal} (hf : AEMeasurable f (volume.restrict (Ioc (0:ℝ) 1))) :
    (∫⁻ s in Ioc (0:ℝ) 1, f s) ^ (2:ℝ) ≤ ∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0:ℝ) 1))
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, one_mul] at hH
  calc (∫⁻ s in Ioc (0:ℝ) 1, f s) ^ (2:ℝ)
      ≤ ((∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ)) ^ (1 / (2:ℝ))) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow hH (by norm_num)
    _ = ∫⁻ s in Ioc (0:ℝ) 1, f s ^ (2:ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num
end ReciprocityTheory.ChartRestriction.DS
