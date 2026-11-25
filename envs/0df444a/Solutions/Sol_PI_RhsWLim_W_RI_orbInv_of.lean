-- Prove2me | solution 1 for PI.RhsWLim.W.RI.orbInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:20.351952+00:00
-- url     : https://prove2.me/submissions/7bf82a48-442a-4eb1-8092-cae8a704acad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvOA
import Theorems.Thm_PI_RhsWLim_W_RI_section_vector_properties
import Theorems.Thm_PI_RhsWLim_W_RI_meas_Ghat
import Theorems.Thm_PI_RhsWLim_W_RI_Gf_fib
import Theorems.Thm_PI_RhsWLim_W_RI_avg_Q
import Theorems.Thm_PI_RhsWLim_W_RI_cont_herm
import Theorems.Thm_PI_RhsWLim_W_RI_rhs_orb
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_circle_ae
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_secP_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution (hQ : HypQ) (hU : UnimodK) (hT : FibTrans) : OrbInv := by
  intro k r z z' μW μW' a a' μsec hd s hs F hF
  have := hd.haarW.1
  have := hd.haarW'.1
  obtain ⟨Q, hσQ, hQi, hQc, c, hc0, hcT, hpol⟩ := hQ k r z z' hd.k_pos hd.z_mem hd.z'_mem hd.T_pos hd.T'_pos
  have hfinW : μW Set.univ ≠ ⊤ := by rw [hd.massW]; exact ENNReal.ofReal_ne_top
  have hnull : Q {v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'} = 0 := by
    have hS : MeasurableSet {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'} :=
      measurableSet_le Complex.continuous_normSq.measurable measurable_const
    have h1 := hpol ({ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator 1) (measurable_one.indicator hS)
    have e : (fun v => ({ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞))
        (herm (Hpk k r) v z)) = ({v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'}).indicator 1 :=
      funext fun v => rfl
    have hmS : MeasurableSet {v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'} :=
      (cont_herm z).measurable hS
    rw [e, lintegral_indicator_one hmS] at h1
    rw [h1]
    have h2 : (fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞) ζ) =ᵐ[volume] 0 := by
      filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
      show ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞) ζ = 0
      by_cases h : Complex.normSq ζ ≤ Tz k r z * Tz k r z'
      · have hlt : Complex.normSq ζ < Tz k r z * Tz k r z' := lt_of_le_of_ne h hζ
        have h0 : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
          unfold zWeight
          rw [if_neg (not_le.2 hlt)]
        rw [h0, ENNReal.ofReal_zero, zero_mul]
      · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_false, mul_zero]
    rw [lintegral_congr_ae h2, Pi.zero_def, lintegral_zero, mul_zero]
  have key : ∀ F' : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞, Measurable F' →
      c * rhsW k r z z' μW μW' μsec (fun x => F' (orbV k r z' x)) =
        ENNReal.ofReal a' * (ENNReal.ofReal a * ∫⁻ v, F' v ∂Q) := by
    intro F' hF'
    have sA : ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * Gf μW F' (embWb k r (μsec ζ) *ᵥ z') =
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * GhatF k r z z' μW μsec F' ζ := by
      refine lintegral_congr_ae ?_
      filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
      by_cases h : Tz k r z * Tz k r z' < Complex.normSq ζ
      · unfold GhatF
        rw [secP_eq h]
      · have h0 : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
          unfold zWeight
          rw [if_neg (not_le.2 (lt_of_le_of_ne (not_lt.1 h) hζ))]
        rw [h0, ENNReal.ofReal_zero, zero_mul, zero_mul]
    have sB : ∫⁻ v, GhatF k r z z' μW μsec F' (herm (Hpk k r) v z) ∂Q = ∫⁻ v, Gf μW F' v ∂Q := by
      refine lintegral_congr_ae ?_
      have hg1 : ∀ᵐ v ∂Q, inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z' := by
        rw [ae_iff]
        exact hQc
      have hg2 : ∀ᵐ v ∂Q, Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) v z) := by
        rw [ae_iff]
        exact measure_mono_null (fun v (hv : ¬ (Tz k r z * Tz k r z' < _)) => not_lt.1 hv) hnull
      filter_upwards [hg1, hg2] with v hv1 hv2
      obtain ⟨p1, p2, p3⟩ := section_vector_properties hd hv2
      unfold GhatF
      rw [secP_eq hv2]
      exact Gf_fib hU hT hd.haarW hfinW hd.z_mem hd.T_pos hF' p1 hv1.1 (p2.trans hv1.2.symm) p3
    rw [rhs_orb hd F', sA, ← hd.massW, ← avg_Q Q hQi hd.haarW hF', ← sB, hpol _ (meas_Ghat hd hF')]
    ring
  have hmv : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have k1 := key (fun v => F (s *ᵥ v)) (hF.comp hmv)
  have k2 := key F hF
  have eQ : ∫⁻ v, F (s *ᵥ v) ∂Q = ∫⁻ v, F v ∂Q := by
    rw [← lintegral_map hF hmv, hQi s hs]
  rw [eQ, ← k2] at k1
  exact (ENNReal.mul_right_inj hc0 hcT).1 k1
end PI.RhsWLim.W.RI
