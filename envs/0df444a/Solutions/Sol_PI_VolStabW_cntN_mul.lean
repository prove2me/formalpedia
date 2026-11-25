-- Prove2me | solution 1 for PI.VolStabW.cntN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:59:23.169209+00:00
-- url     : https://prove2.me/submissions/ff5e14b4-d5da-40aa-924c-c9bcd0c6d502

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
variable [MulAction G Y]
namespace PI.VolStabW
theorem _root_.solution (Γ : Subgroup G) (A : Set G) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    cntN Γ A (γ * g) = cntN Γ A g := by
  unfold cntN
  have e := (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq
    (fun δ : Γ => A.indicator (fun _ => (1 : ℝ≥0∞)) ((δ : G) * g))
  simpa [mul_assoc] using e
end PI.VolStabW
