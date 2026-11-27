-- Prove2me | solution 1 for PI.VolStabSW.meas_cntN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:38.389458+00:00
-- url     : https://prove2.me/submissions/19c8676f-fdc0-4283-9539-4579c669206c

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
variable [MulAction G Y]
namespace PI.VolStabSW
theorem _root_.solution (Γ : Subgroup G) [Countable Γ] {A : Set G} (hA : MeasurableSet A) :
    Measurable (cntN Γ A) := by
  unfold cntN
  exact Measurable.ennreal_tsum fun γ => (measurable_const.indicator hA).comp (measurable_const_mul _)
end PI.VolStabSW
