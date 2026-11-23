-- Prove2me | solution 1 for PI.VolStabSW.HasDens.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:57.694613+00:00
-- url     : https://prove2.me/submissions/7307ff53-1c03-4dc5-addd-9b8ad7bbea9b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen

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
open scoped Pointwise
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
namespace PI.VolStabSW
namespace HasDens
theorem _root_.solution [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) := by
  obtain ⟨i1, c1, e1⟩ := h₁
  obtain ⟨i2, c2, e2⟩ := h₂
  refine ⟨i1.sub i2, c1.sub c2, fun S hS => ?_⟩
  rw [integral_sub i1.integrableOn i2.integrableOn,
    integral_sub (c1.continuousOn.integrableOn_compact hS) (c2.continuousOn.integrableOn_compact hS),
    e1 S hS, e2 S hS]
end HasDens
end PI.VolStabSW
