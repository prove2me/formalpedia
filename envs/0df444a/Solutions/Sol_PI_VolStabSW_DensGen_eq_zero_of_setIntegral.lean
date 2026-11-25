-- Prove2me | solution 1 for PI.VolStabSW.DensGen.eq_zero_of_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:42:49.726859+00:00
-- url     : https://prove2.me/submissions/8e0c0c4b-6153-492a-8eb5-2a74f9ee4d3b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
namespace PI.VolStabSW.DensGen
theorem _root_.solution [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  by_contra hne
  have hpos : 0 < D b0 * D b0 := mul_self_pos.mpr hne
  have hcont : ContinuousAt (fun b => D b0 * D b) b0 :=
    continuousAt_const.mul (hD.continuousAt hW)
  have hev : ∀ᶠ b in 𝓝 b0, D b0 * D b0 / 2 < D b0 * D b :=
    hcont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hW hev)
  have hKW : K ⊆ W := fun x hx => (hKsub hx).1
  have h0K := h0 K hKc hKW
  have hKpos : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
  have hKfin : ν K < ⊤ := hKc.measure_lt_top
  have hint : IntegrableOn D K ν := (hD.mono hKW).integrableOn_compact hKc
  have hle : ∫ b in K, D b0 * D b0 / 2 ∂ν ≤ ∫ b in K, D b0 * D b ∂ν :=
    setIntegral_mono_on (integrableOn_const hKfin.ne) (hint.const_mul (D b0))
      hKc.isClosed.measurableSet (fun b hb => le_of_lt (hKsub hb).2)
  rw [integral_const_mul, h0K, mul_zero, setIntegral_const, smul_eq_mul] at hle
  have hr : 0 < ν.real K := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  have : 0 < ν.real K * (D b0 * D b0 / 2) := mul_pos hr (by linarith)
  linarith
end PI.VolStabSW.DensGen
