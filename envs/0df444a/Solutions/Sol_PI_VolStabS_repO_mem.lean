-- Prove2me | solution 1 for PI.VolStabS.repO_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:28.314512+00:00
-- url     : https://prove2.me/submissions/4e238d1d-eb0c-4643-afe3-78926cc73eb6

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
theorem _root_.solution (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x ∈ Γ := by
  exact (Classical.choose_spec x.2).1
end PI.VolStabS
