-- Prove2me | solution 1 for PI.VolStabSW.densAll_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:50.304278+00:00
-- url     : https://prove2.me/submissions/ad0ffc40-083b-4244-b577-4b305aaf7469

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour

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
open MeasureTheory Topology
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]
namespace PI.VolStabSW
theorem _root_.solution (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    DensAll μ f ι ν U ↔ DensOn (IsCcOn U) μ f ι ν :=
  ⟨fun h φ hφ => h φ hφ.1 hφ.2.1 hφ.2.2, fun h φ h1 h2 h3 => h φ ⟨h1, h2, h3⟩⟩
end PI.VolStabSW
