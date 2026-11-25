-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_lintegral_poincareDeepWeight_lt_top_ad8ff22c8214
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:15.541575+00:00
-- url     : https://prove2.me/submissions/2e2f8614-075b-4714-8e85-815c111daff2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepWeightMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integrableOn_inv_log_sq_mul_30145d823e46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ofReal_mul_poincareDeepWeight_le_a0152c518374

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    ∫⁻ z : ℂ, ENNReal.ofReal (poincareDeepWeight z) < ⊤ := by
  set ρ := Real.exp (-(Real.exp 1 / 2))
  set h : ℝ → ENNReal := (Set.Ioc 0 ρ).indicator
    (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) with hh
  have hm : Measurable h := by
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp
      (((Real.measurable_log.pow_const 2).mul measurable_id).inv.div_const 4)
  rw [← Complex.lintegral_comp_polarCoord_symm]
  calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ENNReal.ofReal (poincareDeepWeight (Complex.polarCoord.symm p))
      ≤ ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, h p.1 * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
        rw [polarCoord_target]
        refine lintegral_mono fun p => ?_
        simp only [poincareDeepWeight, Complex.norm_polarCoord_symm, smul_eq_mul, mul_one, hh]
        exact ofReal_mul_poincareDeepWeight_le p.1
    _ = (∫⁻ r in Set.Ioi 0, h r) * ∫⁻ _ in Set.Ioo (-Real.pi) Real.pi, 1 := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_mul hm.aemeasurable aemeasurable_const
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ?_ ?_
        · refine (setLIntegral_le_lintegral _ _).trans_lt ?_
          rw [hh, lintegral_indicator measurableSet_Ioc]
          exact ((integrableOn_inv_log_sq_mul).div_const 4).lintegral_lt_top
        · rw [setLIntegral_one, Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top
end GroundTheory.Heights₂.Heights
