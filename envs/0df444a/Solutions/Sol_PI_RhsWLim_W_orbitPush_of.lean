-- Prove2me | solution 1 for PI.RhsWLim.W.orbitPush_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:18:18.538229+00:00
-- url     : https://prove2.me/submissions/2687dae9-cc33-4aee-b7b1-9be8f55c2b5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Theorems.Thm_PI_RhsWLim_W_op_volU_pos
import Theorems.Thm_PI_RhsWLim_W_continuous_opOrb
import Theorems.Thm_PI_RhsWLim_W_hypMeas_eq

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
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (h2 : GaugeVolUk) (hK : GaugeK) (hT : TubeLimK) (hI : HypInv) (hR : OrbRepY)
    (hL : HypLocal) (hE : OpEMeas) (hF : HypLF) : OrbitPush := by
  intro k r T' hk hT' νg hνg f hf
  obtain ⟨νK, hνK⟩ := hK k r hk
  obtain ⟨c, hctop, hc⟩ := hR k r T' hk hT' νg hνg (hypM k T')
    (hI k r T' hk hT') (hF k T' hT').1 (hF k T' hT').2
  have hmeas : Measurable (opOrb k r T') := (continuous_opOrb T').measurable
  have hU : 0 < PI.RhsWLim.volU k := op_volU_pos k
  have hK1 : (νK Set.univ).toReal = PI.RhsWLim.volU k := by
    rw [h2 k r νK hνK, ENNReal.toReal_ofReal hU.le]
  have hlim1 := hT k r T' hk hT' νg νK hνg hνK
  rw [hK1] at hlim1
  have hlim2 := hL k r T' hk hT'
  have heqfun : (fun ρ : ℝ => (hypM k T' (opE k r T' ρ)).toReal / tVol k ρ) =
      fun ρ => c.toReal * ((νg (opOrb k r T' ⁻¹' opE k r T' ρ)).toReal / tVol k ρ) := by
    funext ρ
    rw [hc, Measure.smul_apply, Measure.map_apply hmeas (hE k r T' ρ), smul_eq_mul, ENNReal.toReal_mul,
      mul_div_assoc]
  rw [heqfun] at hlim2
  have hkey : T' ^ k / 2 ^ (k + 1) = c.toReal * PI.RhsWLim.volU k :=
    tendsto_nhds_unique hlim2 (hlim1.const_mul c.toReal)
  have hRHS : hypMeas k T' f = c * ∫⁻ p, f p ∂(νg.map (opOrb k r T')) := by
    rw [hypMeas_eq k T' hf, hc, lintegral_smul_measure, smul_eq_mul]
  show ∫⁻ x, f (opOrb k r T' x) ∂νg = _
  rw [← lintegral_map hf hmeas, hRHS, ← mul_assoc]
  have hX : PI.RhsWLim.volU k * 2 ^ (k + 1) / T' ^ k * c.toReal = 1 := by
    have hT'k : (0 : ℝ) < T' ^ k := pow_pos hT' k
    rw [show PI.RhsWLim.volU k * 2 ^ (k + 1) / T' ^ k * c.toReal =
        2 ^ (k + 1) / T' ^ k * (c.toReal * PI.RhsWLim.volU k) by ring, ← hkey]
    field_simp
  have hcc : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
  rw [hcc, ← ENNReal.ofReal_mul (div_pos (mul_pos hU (by positivity)) (pow_pos hT' k)).le, hX,
    ENNReal.ofReal_one, one_mul]
end PI.RhsWLim.W
