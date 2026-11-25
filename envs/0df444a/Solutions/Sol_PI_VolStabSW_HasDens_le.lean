-- Prove2me | solution 1 for PI.VolStabSW.HasDens.le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:20.366175+00:00
-- url     : https://prove2.me/submissions/1288825c-a48f-4558-9624-579f5351ce23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Theorems.Thm_PI_VolStabSW_HasDens_sub
import Theorems.Thm_PI_VolStabSW_nonneg_of_setIntegral

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
theorem _root_.solution [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b := by
  have h := h₂.sub h₁
  have hS : ∀ S, IsCompact S → 0 ≤ ∫ x in S, g₂ x - g₁ x ∂ν := by
    intro S hS
    rw [← h.2.2 S hS]
    exact integral_nonneg fun v => sub_nonneg.mpr (hle v)
  have key : 0 ≤ g₂ b - g₁ b := nonneg_of_setIntegral (fun x => g₂ x - g₁ x) h.2.1 hS b
  linarith
end HasDens
end PI.VolStabSW
