-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.term_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:24.983447+00:00
-- url     : https://prove2.me/submissions/a0d84849-5493-4153-b2f9-0c88713ce3db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
namespace ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
theorem _root_.solution {z : ℂ} {w d la W D : ℝ} (hz : ‖z‖ ≤ la) (hw : |w| ≤ W) (hD : 0 < D) (hd : D ≤ |d|) :
    ‖z * (w : ℂ) / (d : ℂ)‖ ≤ la * W / D := by
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  rw [div_le_div_iff₀ (by linarith) hD]
  have hla : 0 ≤ la := (norm_nonneg _).trans hz
  exact mul_le_mul (mul_le_mul hz hw (abs_nonneg _) hla) hd hD.le (by positivity)
end ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData
