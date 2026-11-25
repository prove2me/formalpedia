-- Prove2me | solution 1 for PI.VolStabSW.repO_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:44.559961+00:00
-- url     : https://prove2.me/submissions/d9d8605d-8413-40b4-b105-b65a03d8db0d

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
theorem _root_.solution (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x ∈ Γ := by
  exact (Classical.choose_spec (x.2 : ∃ γ ∈ Γ, γ • y0 = (x : Y))).1
end PI.VolStabSW
