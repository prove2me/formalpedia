-- Prove2me | solution 1 for SAARate.SharpLD.display_3_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:15:07.368351+00:00
-- url     : https://prove2.me/submissions/43cf8949-17af-4897-b043-15de5147385a

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology BellWilliams2001.ThresholdPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (κ : ℝ) (hκ : 0 < κ)
    (hXκ : ∀ᵐ ω ∂P, |X ω| ≤ κ) :
    ∀ α : ℝ, (((1 / (2 * κ ^ 2)) * |α - ∫ ω, X ω ∂P| ^ 2 : ℝ) : EReal) ≤
      legendre (logMGF P X) α := by
  intro α
  set m : ℝ := ∫ ω, X ω ∂P with hm
  have hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (-κ) κ := by
    filter_upwards [hXκ] with ω hω
    exact abs_le.1 hω
  have hsg := hasSubgaussianMGF_of_mem_Icc hX.aemeasurable hb
  set l : ℝ := (α - m) / κ ^ 2 with hl
  have hcnn : ((((‖κ - -κ‖₊ / 2) ^ 2 : NNReal)) : ℝ) = κ ^ 2 := by
    push_cast
    rw [Real.norm_eq_abs, show κ - -κ = 2 * κ by ring, abs_of_pos (by positivity)]
    ring
  have hmgf : mgf (fun ω => X ω - m) P l ≤ Real.exp (κ ^ 2 * l ^ 2 / 2) := by
    have := hsg.mgf_le l
    rw [hcnn] at this
    exact this
  have hint : Integrable (fun ω => Real.exp (l * X ω)) P := by
    have h1 := (hsg.integrable_exp_mul l).const_mul (Real.exp (l * m))
    refine h1.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [← Real.exp_add]; congr 1; ring
  have hI : ∫ ω, Real.exp (l * X ω) ∂P = Real.exp (l * m) * mgf (fun ω => X ω - m) P l := by
    unfold mgf
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [← Real.exp_add]; congr 1; ring
  have hIpos : 0 < ∫ ω, Real.exp (l * X ω) ∂P := by
    have := mgf_pos' (μ := P) (X := X) (IsProbabilityMeasure.ne_zero P) hint (t := l)
    simpa [mgf] using this
  have hlog : logMGF P X l = ((Real.log (∫ ω, Real.exp (l * X ω) ∂P) : ℝ) : EReal) := by
    unfold logMGF
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    rw [ENNReal.log_ofReal_of_pos hIpos]
  have hle : Real.log (∫ ω, Real.exp (l * X ω) ∂P) ≤ l * m + κ ^ 2 * l ^ 2 / 2 := by
    rw [Real.log_le_iff_le_exp hIpos, hI, Real.exp_add]
    exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
  refine le_iSup_of_le l ?_
  rw [hlog]
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  have : (1 / (2 * κ ^ 2)) * |α - m| ^ 2 = l * α - (l * m + κ ^ 2 * l ^ 2 / 2) := by
    rw [hl, sq_abs]
    field_simp
    ring
  rw [this]
  linarith
