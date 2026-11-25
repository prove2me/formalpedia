-- Prove2me | solution 1 for PI.RhsWLim.W.rhsTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:14.418643+00:00
-- url     : https://prove2.me/submissions/9a70ac80-f682-4bf5-a900-69fc57fafa75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Theorems.Thm_PI_RhsWLim_W_herm_emb
import Theorems.Thm_PI_RhsWLim_W_herm_fix
import Theorems.Thm_PI_RhsWLim_W_inv_fix
import Theorems.Thm_PI_RhsWLim_W_circle_null
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
private theorem pairF_mul_embWb_mul_inv {z z' : Fin (2 * r + k + 1) → ℂ} (hz : PI.RhsWLim.inWb k r z) (hz' : PI.RhsWLim.inWb k r z')
    {p q : PI.RhsWLim.Mat k r} (hp : p ∈ PI.RhsWLim.UWset k r z) (hq : q ∈ PI.RhsWLim.UWset k r z')
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    pairF k r z z' (fun i j => (p * PI.RhsWLim.embWb k r μ * q⁻¹) i j) =
      PI.RhsWLim.herm (PI.RhsWLim.Hb k) (μ *ᵥ PI.RhsWLim.wbPart k r z') (PI.RhsWLim.wbPart k r z) := by
  show PI.RhsWLim.herm (PI.RhsWLim.Hpk k r) ((p * PI.RhsWLim.embWb k r μ * q⁻¹) *ᵥ z') z = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, herm_fix hp,
    inv_fix hq, herm_emb μ z z' hz hz']
end PI.RhsWLim.W
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution : RhsTest := by
  intro k r z z' μW μW' a a' μsec hD g hg
  simp only [PI.RhsWLim.rhsW]
  obtain ⟨-, -, hnW, -⟩ := hD.haarW
  obtain ⟨-, -, hnW', -⟩ := hD.haarW'
  obtain ⟨-, hS⟩ := hD.sec
  have hW : ∀ᵐ x ∂μW, Matrix.of x ∈ PI.RhsWLim.UWset k r z := ae_iff.mpr hnW
  have hW' : ∀ᵐ x ∂μW', Matrix.of x ∈ PI.RhsWLim.UWset k r z' := ae_iff.mpr hnW'
  have hae : ∀ᵐ ζ : ℂ, Complex.normSq ζ ≠ PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' := by
    rw [ae_iff]
    simpa using circle_null (PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z')
  rw [← lintegral_const_mul' (ENNReal.ofReal (a * a')) _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hae] with ζ hζ
  try dsimp only
  by_cases hreg : PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' < Complex.normSq ζ
  · have hsec := (hS ζ hreg).2
    rw [lintegral_congr_ae (μ := μW) (g := fun _ => g ζ * ENNReal.ofReal a') ?_]
    · rw [lintegral_const, hD.massW, ENNReal.ofReal_mul hD.a_pos.le]
      ring
    · filter_upwards [hW] with h hh
      try dsimp only
      rw [lintegral_congr_ae (μ := μW') (g := fun _ => g ζ) ?_]
      · rw [lintegral_const, hD.massW']
      · filter_upwards [hW'] with h' hh'
        exact (congrArg g (pairF_mul_embWb_mul_inv hD.z_mem hD.z'_mem hh hh' (μsec ζ))).trans (congrArg g hsec)
  · have hle : ¬ (PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' ≤ Complex.normSq ζ) :=
      fun hle => hreg (lt_of_le_of_ne hle (Ne.symm hζ))
    have h0 : PI.RhsWLim.zWeight k (PI.RhsWLim.Tz k r z) (PI.RhsWLim.Tz k r z') ζ = 0 := by
      unfold PI.RhsWLim.zWeight
      exact if_neg hle
    simp [h0]
end PI.RhsWLim.W
