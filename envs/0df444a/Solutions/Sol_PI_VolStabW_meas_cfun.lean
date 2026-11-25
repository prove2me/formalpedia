-- Prove2me | solution 1 for PI.VolStabW.meas_cfun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:46.862809+00:00
-- url     : https://prove2.me/submissions/fc3bc67c-0d76-4224-bd67-7f133e85b8dd

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
theorem _root_.solution (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by
  unfold cfun
  exact Measurable.ennreal_tsum fun x =>
    (measurable_const.indicator hA).comp ((measurable_const_mul (repO Γ y0 x)).comp measurable_inv)
end PI.VolStabW
