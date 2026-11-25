-- Prove2me | solution 1 for PI.VolStabSW.nonneg_of_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:23.024634+00:00
-- url     : https://prove2.me/submissions/b76a5dc0-210b-4153-8dad-0066772c318f

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
theorem _root_.solution [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  push_neg at hneg
  have hU : {b | D b < D b0 / 2} ∈ 𝓝 b0 :=
    (isOpen_lt hD continuous_const).mem_nhds (by show D b0 < D b0 / 2; linarith)
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hpos : 0 < ν K := ν.measure_pos_of_mem_nhds hKn
  have hfin : ν K < ⊤ := hKc.measure_lt_top
  have h1 : ∫ b in K, D b ∂ν ≤ ∫ b in K, D b0 / 2 ∂ν :=
    setIntegral_mono_on (hD.continuousOn.integrableOn_compact hKc)
      (continuousOn_const.integrableOn_compact hKc) hKc.measurableSet
      (fun x hx => le_of_lt (hKU hx))
  rw [setIntegral_const, smul_eq_mul] at h1
  try simp only [Measure.real] at h1
  have h2 : 0 < (ν K).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have h3 := h0 K hKc
  nlinarith
end PI.VolStabSW
