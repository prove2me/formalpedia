-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFibreAverage_proof_95276225f000
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:02.285613+00:00
-- url     : https://prove2.me/submissions/bfb4402b-26a7-443f-a90c-bfffea0dbe4a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_real_smul_mem_coneSet_09cb40c5598f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneFibreAverage_of_lt_6291d9b63762
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneFibreAverage_zero_628f6f8200cc

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeFibreAverage
theorem _root_.solution (hA : ConeAreaFormula.Statement) (hT : ConeTangentAverage.Statement)
    (hR : ConeRadialIntegral.Statement) (hG : TangentGaussMoment.Statement) :
    ConeFibreAverage.Statement := by
  intro n m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1), Metric.measure_ball_pos _ _ one_pos,
      measure_ball_lt_top, fun h J hJ hfib => coneFibreAverage_zero h J hJ hfib⟩
  by_cases hmn : m ≤ n
  swap
  · exact ⟨1, one_pos, ENNReal.one_lt_top, fun h J _ _ => coneFibreAverage_of_lt (by omega) h J⟩
  obtain ⟨hkm, hkanti, hkpos, hM0, hMtop⟩ := hG n m hm hmn
  set μ := Measure.hausdorffMeasure (X := EuclideanSpace ℂ (Fin n)) ((2 * m : ℕ) : ℝ) with hμ
  set k := tangentGaussProfile n m with hk
  set M := ∫⁻ r in Set.Ioi (0 : ℝ), k r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) with hM
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨H, hHdef⟩ : ∃ H, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = H := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = V := ⟨_, rfl⟩
  have hH0 : H ≠ 0 := by
    rw [← hHdef, hd]
    exact (Metric.measure_ball_pos _ _ one_pos).ne'
  have hHtop : H ≠ ⊤ := by
    rw [← hHdef, hd]
    exact measure_ball_lt_top.ne
  have hV0 : V ≠ 0 := hVdef ▸ (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ⊤ := hVdef ▸ measure_ball_lt_top.ne
  have hc0 : H⁻¹ * V ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.2 hHtop) hV0
  have hctop : H⁻¹ * V ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hH0) hVtop
  refine ⟨H⁻¹ * V * M, ENNReal.mul_pos hc0 hM0.ne', ENNReal.mul_lt_top hctop.lt_top hMtop, ?_⟩
  intro h J hJ hfib

  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
        H⁻¹ * V * ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y) ∂μ := by
    intro π
    have harea := hA n m h J hJ hm hmn hfib π ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1)
      (measurable_one.indicator Metric.isOpen_ball.measurableSet)
    have hind : ∫⁻ w, (fibreCount h J π w : ℝ≥0∞) * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 w = ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) := by
      rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
      congr 1
      funext w
      by_cases hw : w ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1 <;> simp [hw]
    rw [hind, hVdef, hHdef] at harea
    rw [mul_assoc, harea, ← mul_assoc, ENNReal.inv_mul_cancel hH0 hHtop, one_mul]
  have hlhs : ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      H⁻¹ * V * ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
    rw [← hT n m h J hJ hm hmn hfib, ← lintegral_const_mul' _ _ hctop]
    refine lintegral_congr fun π => ?_
    rw [hin π]
    ring
  rw [hlhs]
  by_cases hfin : μ {y | ‖y‖ < 1 ∧ y ∈ coneSet h J} < ⊤
  · rw [hR n m hm (coneSet h J) (fun y hy t _ => real_smul_mem_coneSet h hJ hy t) hfin k hkm]
    ring
  · rw [not_lt, top_le_iff] at hfin
    rw [hfin, ENNReal.mul_top (ENNReal.mul_pos hc0 hM0.ne').ne']
    have hball : MeasurableSet {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} :=
      measurableSet_lt measurable_norm measurable_const
    have hge : k 1 * ⊤ ≤ ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
      calc k 1 * ⊤ = ∫⁻ y in coneSet h J, {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1}.indicator
              (fun _ => k 1) y ∂μ := by
            rw [lintegral_indicator_const hball, Measure.restrict_apply hball]
            congr 1
            exact hfin.symm
        _ ≤ ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
            refine lintegral_mono fun y => ?_
            by_cases hy : ‖y‖ < 1
            · rw [Set.indicator_of_mem (show y ∈ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} from hy)]
              exact hkanti (Set.mem_Ici.2 (norm_nonneg y)) (Set.mem_Ici.2 zero_le_one) hy.le
            · rw [Set.indicator_of_notMem (show y ∉ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} from hy)]
              exact bot_le
    rw [ENNReal.mul_top (hkpos 1).ne', top_le_iff] at hge
    rw [hge, ENNReal.mul_top hc0]
end ConeFibreAverage
end GroundTheory.Heights₂.Heights
