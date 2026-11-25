-- Prove2me | solution 1 for PI.VolStabSW.repO_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:47.90132+00:00
-- url     : https://prove2.me/submissions/df5f39f8-c63f-4f9d-a972-50120f6f5800

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
theorem _root_.solution (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x • y0 = x := by
  exact (Classical.choose_spec (x.2 : ∃ γ ∈ Γ, γ • y0 = (x : Y))).2
end PI.VolStabSW
