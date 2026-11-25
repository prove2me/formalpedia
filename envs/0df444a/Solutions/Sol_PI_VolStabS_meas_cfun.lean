-- Prove2me | solution 1 for PI.VolStabS.meas_cfun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:51:08.909196+00:00
-- url     : https://prove2.me/submissions/34eb6293-1890-4f0b-88e9-ce90fa2d66cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_UnfoldAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable [MulAction G Y]
namespace PI.VolStabS
theorem _root_.solution (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by
  unfold cfun
  exact Measurable.ennreal_tsum fun x =>
    (measurable_const.indicator hA).comp ((measurable_const_mul (repO Γ y0 x)).comp measurable_inv)
end PI.VolStabS
