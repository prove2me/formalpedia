-- Prove2me | solution 1 for PI.VolStabW.cosApx_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:59:47.736109+00:00
-- url     : https://prove2.me/submissions/e2d0289a-db75-45e1-832c-9a87b5d4478c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGen

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
open MeasureTheory Topology Set Filter
open scoped Pointwise
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
namespace PI.VolStabW
theorem _root_.solution (Λ : AddSubgroup V) (x : V) : -((x : V ⧸ Λ).out) + x ∈ Λ :=
  QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (x : V ⧸ Λ))
end PI.VolStabW
