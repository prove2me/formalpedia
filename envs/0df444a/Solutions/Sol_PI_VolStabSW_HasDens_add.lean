-- Prove2me | solution 1 for PI.VolStabSW.HasDens.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:06.268059+00:00
-- url     : https://prove2.me/submissions/6ff0d50d-b772-4fc8-b857-a4fe840982c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos

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
open MeasureTheory Topology Set Filter
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
namespace PI.VolStabSW
namespace HasDens
theorem _root_.solution [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v + φ₂ v) (fun b => g₁ b + g₂ b) := by
  obtain ⟨hi1, hc1, he1⟩ := h₁
  obtain ⟨hi2, hc2, he2⟩ := h₂
  refine ⟨hi1.add hi2, hc1.add hc2, fun S hS => ?_⟩
  have hg1 : IntegrableOn g₁ S ν := by
    first
      | exact hc1.continuousOn.integrableOn_compact hS
      | exact ContinuousOn.integrableOn_compact hS hc1.continuousOn
  have hg2 : IntegrableOn g₂ S ν := by
    first
      | exact hc2.continuousOn.integrableOn_compact hS
      | exact ContinuousOn.integrableOn_compact hS hc2.continuousOn
  rw [integral_add hi1.integrableOn hi2.integrableOn, integral_add hg1 hg2, he1 S hS, he2 S hS]
end HasDens
end PI.VolStabSW
