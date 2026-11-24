-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeIntegralLine_proof_ffc40bccdc87
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:13.915726+00:00
-- url     : https://prove2.me/submissions/c152b824-2e0f-4092-91d7-7597d78fcf1d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_continuous_pointOf_0847939ca07e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_pointOf_eq_zero_1a71672ffe50

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ConeIntegralLine
theorem _root_.solution : ConeIntegralLine.Statement := by
  intro n h W y₀ hline φ hφ
  unfold coneIntegral
  set S := {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0} with hS
  have hSm : MeasurableSet S := by
    have hS' : S = {y | ‖y‖ < 1} ∩ ⋂ q ∈ W, {y | eval (h.pointOf y) q = 0} := by
      ext y; simp [S]
    rw [hS']
    exact (isOpen_lt continuous_norm continuous_const).measurableSet.inter
      (isClosed_biInter fun q _ =>
        isClosed_eq ((continuous_eval q).comp h.continuous_pointOf) continuous_const).measurableSet
  have h0 : Measure.hausdorffMeasure (((2 * (0 + 1) : ℕ) : ℝ))
      ({0} : Set (EuclideanSpace ℂ (Fin n))) = 0 := by
    have := hausdorffMeasure_of_dimH_lt (X := EuclideanSpace ℂ (Fin n)) (s := {0}) (d := 2)
      (by rw [dimH_singleton]; norm_num)
    simpa using this
  have hne : ∀ᵐ y ∂(Measure.hausdorffMeasure (((2 * (0 + 1) : ℕ) : ℝ)) :
      Measure (EuclideanSpace ℂ (Fin n))), y ≠ 0 := by
    rw [ae_iff]; simpa using h0
  have hae : ∀ᵐ y ∂(Measure.hausdorffMeasure (((2 * (0 + 1) : ℕ) : ℝ)) :
      Measure (EuclideanSpace ℂ (Fin n))), y ∈ S → φ (h.pointOf y) = φ y₀ := by
    filter_upwards [hne] with y hy hyS
    obtain ⟨t, ht⟩ := (hline _).1 hyS.2
    have htne : t ≠ 0 := by
      rintro rfl
      exact hy (h.pointOf_eq_zero (by simpa using ht))
    rw [ht, hφ t htne]
  rw [setIntegral_congr_ae hSm hae, setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  ring
end ConeIntegralLine
end GroundTheory.Heights₂.Heights
