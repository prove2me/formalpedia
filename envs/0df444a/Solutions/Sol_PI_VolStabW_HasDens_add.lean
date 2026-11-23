-- Prove2me | solution 1 for PI.VolStabW.HasDens.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:25.717463+00:00
-- url     : https://prove2.me/submissions/d87201da-7323-45cc-b16d-e3c5a6735ba8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCos

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
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
namespace PI.VolStabW
namespace HasDens
theorem _root_.solution [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v + φ₂ v) (fun b => g₁ b + g₂ b) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun S hS => ?_⟩
  rw [integral_add h₁.1.integrableOn h₂.1.integrableOn, h₁.2.2 S hS, h₂.2.2 S hS,
    integral_add (h₁.2.1.continuousOn.integrableOn_compact hS)
      (h₂.2.1.continuousOn.integrableOn_compact hS)]
end HasDens
end PI.VolStabW
