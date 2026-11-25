-- Prove2me | solution 1 for PI.IsoInvMetricW.isoInvMetric_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:43.613001+00:00
-- url     : https://prove2.me/submissions/362797cd-f26d-462f-96b8-ad053b0a7db2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_PI_IsoInvMetricW_symmetricMeasure_l2Norm_eq_resolutionL2
import Theorems.Thm_PI_IsoInvMetricW_ipl_zero_left
import Theorems.Thm_PI_IsoInvMetricW_ipl_add_left
import Theorems.Thm_PI_IsoInvMetricW_ipl_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoInvMetricW
theorem _root_.solution (hU : Unit) (hI : InvK) (hS : Stab) (hH : HvCols) (hN : Norm1)
    (hG : Gen) (hW : HW) : IsoInvMetric := by
  intro Lt _ _ N nu
  refine ⟨fun k hk => ⟨fun φ hφ => ⟨hS Lt N nu k φ hφ, ?_⟩, fun hle => ?_⟩, fun ip hip => ?_⟩
  · apply Complex.ofReal_injective
    rw [symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk]
  · rw [hH Lt N nu k]
    apply Complex.ofReal_injective
    rw [symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk, ← symmetricMeasure_l2Norm_eq_resolutionL2, hN Lt N nu hle]
  · have hu : u0 N nu ∈ Vnu N nu := Submodule.subset_span ⟨_, rfl⟩
    have key : ∀ φ ∈ Vnu N nu, ∀ ψ ∈ Vnu N nu, ip φ ψ = ipl φ ψ := by
      intro φ hφ ψ hψ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        obtain ⟨k, hk, c, hc⟩ := hG Lt N nu y
        obtain ⟨ψ', hψ', e1⟩ : ∃ ψ', ψ' ∈ Vnu N nu ∧ ψ = VnuMap nu k ψ' :=
          ⟨_, hS Lt N nu _ ψ hψ, (hI Lt N nu k hk ψ).symm⟩
        have h2 : ip (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') =
            ipl (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') := by
          rw [(hip k hk).1 _ hu _ hψ', hW Lt N nu ip hip ψ' hψ', hU Lt N nu k hk]
        rw [hc, hH Lt N nu k, LinearMap.map_smulₛₗ₂, ipl_smul_left, e1, h2, smul_eq_mul]
      | zero => simp [ipl_zero_left]
      | add x y _ _ hx hy => rw [LinearMap.map_add₂, hx, hy, ipl_add_left]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, ipl_smul_left, smul_eq_mul]
    intro φ hφ
    rw [symmetricMeasure_l2Norm_eq_resolutionL2]
    exact key φ hφ φ hφ
end PI.IsoInvMetricW
