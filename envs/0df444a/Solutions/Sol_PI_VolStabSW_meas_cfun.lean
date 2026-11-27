-- Prove2me | solution 1 for PI.VolStabSW.meas_cfun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:34.776929+00:00
-- url     : https://prove2.me/submissions/e4e025f9-08bd-4104-a411-50a0e00335c9

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
theorem _root_.solution (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by
  unfold cfun
  exact Measurable.ennreal_tsum fun x =>
    (measurable_const.indicator hA).comp ((measurable_const_mul _).comp measurable_inv)
end PI.VolStabSW
