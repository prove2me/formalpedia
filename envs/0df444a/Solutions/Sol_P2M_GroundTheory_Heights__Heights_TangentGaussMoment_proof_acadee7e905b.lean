-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentGaussMoment_proof_acadee7e905b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:00.253874+00:00
-- url     : https://prove2.me/submissions/16cebe07-76f9-4549-85bc-9d803e9b6d67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tangentGaussProfile_antitoneOn_60715fa850a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_tangentGaussProfile_fdaff60c6dae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_pow_two_mul_sub_one_le_dcc969861cb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ae_coordPlaneBlock_det_ne_zero_029df6309a2e


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
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TangentGaussMoment
theorem _root_.solution (hA : LeadPlaneJac.Statement) (hB : LeadBlockGaussTail.Statement) :
    TangentGaussMoment.Statement := by
  intro n m hm hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hk : ∀ r : ℝ, tangentGaussProfile (m + k) m r = ∫⁻ π : Fin m → Fin (m + k) → ℂ, matGauss π *
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
      ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) := by
    intro r
    unfold tangentGaussProfile
    simp only [hA m k]
  have hpos : ∀ r : ℝ, 0 < tangentGaussProfile (m + k) m r := by
    intro r
    rw [hk r]
    have hcont : Continuous fun π : Fin m → Fin (m + k) → ℂ =>
        linProj π ((r : ℂ) • firstCoordVec (m + k)) := by
      unfold linProj
      exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
    have hdet : Continuous fun π : Fin m → Fin (m + k) → ℂ => (coordPlaneBlock π).det :=
      Continuous.matrix_det (by unfold coordPlaneBlock; fun_prop)
    have hmeas : Measurable fun π : Fin m → Fin (m + k) → ℂ => matGauss π *
        (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
          (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) ?_
      · unfold matGauss
        exact ENNReal.measurable_ofReal.comp (by fun_prop)
      · exact (measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hcont.measurable
      · exact ENNReal.measurable_ofReal.comp ((continuous_norm.comp hdet).pow 2).measurable
    rw [lintegral_pos_iff_support hmeas]
    set U := {π : Fin m → Fin (m + k) → ℂ |
      linProj π ((r : ℂ) • firstCoordVec (m + k)) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1}
    have hU : IsOpen U := Metric.isOpen_ball.preimage hcont
    have hU0 : (0 : Fin m → Fin (m + k) → ℂ) ∈ U := by
      have h0 : linProj (0 : Fin m → Fin (m + k) → ℂ) ((r : ℂ) • firstCoordVec (m + k)) = 0 := by
        ext i
        simp [linProj]
      simp only [U, Set.mem_ofPred_eq, h0, Metric.mem_ball, dist_self, zero_lt_one]
    have : (volume : Measure (Fin m → Fin (m + k) → ℂ)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    refine (hU.measure_pos volume ⟨0, hU0⟩).trans_le (measure_mono_ae ?_)
    filter_upwards [ae_coordPlaneBlock_det_ne_zero m k] with π hπdet hπU
    show matGauss π * _ * _ ≠ 0
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    · rw [Set.indicator_of_mem hπU]
      exact one_ne_zero
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨C, hC⟩ := hB m k hm
  have hmeasM : Measurable fun r : ℝ =>
      tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) :=
    (measurable_tangentGaussProfile _ _).mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  refine ⟨measurable_tangentGaussProfile _ _, tangentGaussProfile_antitoneOn _ _, hpos, ?_, ?_⟩
  · rw [setLIntegral_pos_iff hmeasM]
    have hsub : Set.Ioi (0 : ℝ) ⊆
        Function.support (fun r : ℝ =>
          tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))) ∩
          Set.Ioi 0 := by
      intro r hr
      refine ⟨?_, hr⟩
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      exact mul_ne_zero (hpos r).ne' (ENNReal.ofReal_pos.2 (by
        have := Set.mem_Ioi.1 hr
        positivity)).ne'
    exact lt_of_lt_of_le (by simp) (measure_mono hsub)
  · have hle : ∀ r ∈ Set.Ioi (0 : ℝ),
        tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ≤
          ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by
      intro r hr
      have hr0 : 0 ≤ r := le_of_lt hr
      have h1 := pow_two_mul_sub_one_le hr0 m
      have hx : 0 < 1 + r ^ 2 := by positivity
      have hC0 : 0 ≤ max C 0 := le_max_right _ _
      calc tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
          ≤ ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1)) * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) := by
            rw [hk r]
            gcongr
            exact hC r
        _ = ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))) :=
            (ENNReal.ofReal_mul' (by positivity)).symm
        _ ≤ ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))
                ≤ max C 0 / (1 + r ^ 2) ^ (m + 1) * (2 * m * (1 + r ^ 2) ^ m) := by
                  gcongr
                  exact le_max_left _ _
              _ = 2 * m * max C 0 * (1 + r ^ 2)⁻¹ := by
                  field_simp
                  ring
    calc ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
        ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) :=
          setLIntegral_mono' measurableSet_Ioi hle
      _ ≤ ∫⁻ r, ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := setLIntegral_le_lintegral _ _
      _ < ⊤ := (integrable_inv_one_add_sq.const_mul _).lintegral_lt_top
end TangentGaussMoment
end GroundTheory.Heights₂.Heights
