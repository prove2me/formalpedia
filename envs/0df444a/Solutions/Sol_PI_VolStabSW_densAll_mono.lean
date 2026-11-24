-- Prove2me | solution 1 for PI.VolStabSW.densAll_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.985176+00:00
-- url     : https://prove2.me/submissions/e35f1be8-3193-4e13-ba2f-7b57c03ccf2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibOfTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfSt

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]
namespace PI.VolStabSW
theorem _root_.solution {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X} {U U' : Set V}
    (h : DensAll μ f ι ν U') (hU : U ⊆ U') : DensAll μ f ι ν U := by
  intro φ hc hs hφ
  exact h φ hc hs (hφ.trans hU)
end PI.VolStabSW
