-- Prove2me | solution 1 for PI.RhsWLim.W.hypLocal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:23:55.935626+00:00
-- url     : https://prove2.me/submissions/f872141e-0f33-4607-9320-715104a0ad9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartJac
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution (hJ : ChartJac) (hC : HypChart) (hD : PhiDiff) : HypLocal := by
  intro k r T' hk hT
  obtain ⟨hcd, hdet⟩ := hD k r T' hk hT
  obtain ⟨ε, hε, hV⟩ := hC k r T' hk hT
  have hdet0 : (fderiv ℝ (phiT k r T') 0).det ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (by positivity)
  have hlim := hJ (TrE k) (phiT k r T') volume (fun _ => 1) hcd hdet0
    continuousAt_const ENNReal.one_ne_top ⟨Set.univ, Filter.univ_mem, fun A _ _ => by simp⟩
  have key := hlim.const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ((1 : ℝ≥0∞).toReal * |(fderiv ℝ (phiT k r T') 0).det|) =
      T' ^ k / 2 ^ (k + 1) := by
    rw [hdet, ENNReal.toReal_one, one_mul, abs_of_pos (by positivity), div_pow, pow_succ]
    field_simp
    try ring
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε)] with ρ hρ0 hρε
  rw [hV ρ hρ0 hρε, tVol, ENNReal.toReal_mul, mul_div_assoc]
  congr 1
  simp
end PI.RhsWLim.W
