-- Prove2me | solution 1 for PI.VolStabW.nonneg_of_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:02:57.324736+00:00
-- url     : https://prove2.me/submissions/624da906-fbb0-4b63-8279-1e5e0c3753e3

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
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
namespace PI.VolStabW
theorem _root_.solution [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  rw [not_le] at hneg
  have hev : ∀ᶠ b in 𝓝 b0, D b < D b0 / 2 :=
    hD.continuousAt.eventually (gt_mem_nhds (by linarith))
  obtain ⟨S, hSn, hSsub, hSc⟩ := local_compact_nhds hev
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hlt : ν S ≠ ⊤ := hSc.measure_lt_top.ne
  have hpos' : 0 < ν.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ν.measure_pos_of_mem_nhds hSn).ne' hlt
  have hge := setIntegral_ge_of_const_le_real (c := -(D b0 / 2)) (f := fun b => -D b) hSm hlt
    (fun b hb => by
      have : D b < D b0 / 2 := hSsub hb
      linarith)
    (hD.neg.continuousOn.integrableOn_compact hSc)
  rw [integral_neg] at hge
  have := h0 S hSc
  nlinarith
end PI.VolStabW
