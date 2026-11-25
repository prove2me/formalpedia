-- Prove2me | solution 1 for PI.VolStabW.cosApx_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:08:38.444283+00:00
-- url     : https://prove2.me/submissions/3380524c-471c-43c1-a2ee-3c2991cef4ba

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
theorem _root_.solution (Λ : AddSubgroup V) (φ : V → ℝ) {x y : V} (h : -x + y ∈ Λ) :
    cosApx Λ φ y = cosApx Λ φ x :=
  congrArg (fun q : V ⧸ Λ => φ q.out) (QuotientAddGroup.eq.2 h).symm
end PI.VolStabW
