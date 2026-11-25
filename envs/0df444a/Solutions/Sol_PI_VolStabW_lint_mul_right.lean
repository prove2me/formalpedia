-- Prove2me | solution 1 for PI.VolStabW.lint_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:16.399571+00:00
-- url     : https://prove2.me/submissions/374edf63-f6b9-4697-82ac-f862793586fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
namespace PI.VolStabW
theorem _root_.solution {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (f : G → ℝ≥0∞) (r : G) : ∫⁻ g, f (g * r) ∂μ = ∫⁻ g, f g ∂μ := by
  calc ∫⁻ g, f (g * r) ∂μ = ∫⁻ g, f (g⁻¹ * r) ∂μ := (lintegral_inv_eq_self (fun g => f (g * r))).symm
    _ = ∫⁻ g, (fun h => f h⁻¹) (r⁻¹ * g) ∂μ := by
      congr 1
      funext g
      simp [mul_inv_rev]
    _ = ∫⁻ g, f g⁻¹ ∂μ := lintegral_mul_left_eq_self (fun h => f h⁻¹) r⁻¹
    _ = ∫⁻ g, f g ∂μ := lintegral_inv_eq_self f
end PI.VolStabW
