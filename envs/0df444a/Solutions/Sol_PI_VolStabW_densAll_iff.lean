-- Prove2me | solution 1 for PI.VolStabW.densAll_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:37.946236+00:00
-- url     : https://prove2.me/submissions/55660610-e00d-4ded-80c4-48d03b56663b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour

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
open MeasureTheory Topology
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]
namespace PI.VolStabW
theorem _root_.solution (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    DensAll μ f ι ν U ↔ DensOn (IsCcOn U) μ f ι ν := by
  constructor
  · intro h φ hφ; exact h φ hφ.1 hφ.2.1 hφ.2.2
  · intro h φ h1 h2 h3; exact h φ ⟨h1, h2, h3⟩
end PI.VolStabW
