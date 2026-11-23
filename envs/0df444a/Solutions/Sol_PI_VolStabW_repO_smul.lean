-- Prove2me | solution 1 for PI.VolStabW.repO_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:55.615355+00:00
-- url     : https://prove2.me/submissions/85b22942-09c5-4733-8fde-1be2a43fa5e2

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
theorem _root_.solution (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x • y0 = x := by
  exact (Classical.choose_spec x.2).2
end PI.VolStabW
