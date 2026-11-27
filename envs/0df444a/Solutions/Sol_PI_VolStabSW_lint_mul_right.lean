-- Prove2me | solution 1 for PI.VolStabSW.lint_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:20:06.571567+00:00
-- url     : https://prove2.me/submissions/0d215f44-5bcb-40c6-a0f6-db6964095b5f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnfoldAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
namespace PI.VolStabSW
theorem _root_.solution {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (f : G → ℝ≥0∞) (r : G) : ∫⁻ g, f (g * r) ∂μ = ∫⁻ g, f g ∂μ := by
  calc ∫⁻ g, f (g * r) ∂μ = ∫⁻ g, f (g⁻¹ * r) ∂μ := (lintegral_inv_eq_self (fun g => f (g * r))).symm
    _ = ∫⁻ g, (fun x => f x⁻¹) (r⁻¹ * g) ∂μ := by simp [mul_inv_rev]
    _ = ∫⁻ g, f g⁻¹ ∂μ := lintegral_mul_left_eq_self (fun x => f x⁻¹) r⁻¹
    _ = ∫⁻ g, f g ∂μ := lintegral_inv_eq_self f
end PI.VolStabSW
