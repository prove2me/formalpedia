-- Prove2me | solution 1 for PI.VolStabW.LocPosW.pos_of_lb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:57:17.871652+00:00
-- url     : https://prove2.me/submissions/1ba81cf1-0441-4c4f-8250-6ae6a2cc9f0e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FreeOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensPos

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set
open scoped TensorProduct ENNReal
open PI.VolStabW.LocPosW
namespace PI.VolStabW.LocPosW
theorem _root_.solution {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} (hι : Function.Injective ι)
    {U : Set V} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    {f' : V → X} (hf' : Continuous f') (hff : ∀ v, f v = ι (f' v))
    {φ : V → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ v, 0 ≤ φ v) {W : Set V} (hWU : W ⊆ U) {δ : ℝ} (hδ : 0 < δ)
    (hWφ : ∀ v ∈ W, δ ≤ φ v) {b0 : X} {c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ⊤) {N : Set X}
    (hN : N ∈ 𝓝 b0) (hlb : ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W))
    (hνpos : ∀ O : Set X, IsOpen O → O.Nonempty → ν O ≠ 0) (hνfin : ∃ N' ∈ 𝓝 b0, ν N' < ⊤) :
    0 < ∫ v, φ v ∂(fib b0) := by
  obtain ⟨hsupp, hdis, hcont⟩ := hfib
  obtain ⟨hint, hIc⟩ := hcont φ hφc hφs hφU
  have hIcont : Continuous (fun b => ∫ v, φ v ∂(fib b)) := continuousOn_univ.mp hIc
  have hI0 : ∀ b, 0 ≤ ∫ v, φ v ∂(fib b) := fun b => integral_nonneg hφ0
  by_contra hneg
  push_neg at hneg
  have hb0 : ∫ v, φ v ∂(fib b0) = 0 := le_antisymm hneg (hI0 b0)
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hc'
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = c.toReal * δ / 2 := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hO : {b | ∫ v, φ v ∂(fib b) < ε} ∈ 𝓝 b0 :=
    hIcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hb0]; exact hεpos))
  obtain ⟨N', hN', hN'fin⟩ := hνfin
  obtain ⟨S, hSdef⟩ : ∃ S : Set X,
      S = interior N ∩ interior N' ∩ interior {b | ∫ v, φ v ∂(fib b) < ε} := ⟨_, rfl⟩
  have hSo : IsOpen S := by
    rw [hSdef]
    exact (isOpen_interior.inter isOpen_interior).inter isOpen_interior
  have hb0S : b0 ∈ S := by
    rw [hSdef]
    exact ⟨⟨mem_interior_iff_mem_nhds.mpr hN, mem_interior_iff_mem_nhds.mpr hN'⟩,
      mem_interior_iff_mem_nhds.mpr hO⟩
  have hSN : S ⊆ N := by
    rw [hSdef]
    exact fun b hb => interior_subset hb.1.1
  have hSN' : S ⊆ N' := by
    rw [hSdef]
    exact fun b hb => interior_subset hb.1.2
  have hSε : ∀ b ∈ S, ∫ v, φ v ∂(fib b) < ε := by
    rw [hSdef]
    exact fun b hb => interior_subset (s := {b | ∫ v, φ v ∂(fib b) < ε}) hb.2
  have hSm : MeasurableSet S := hSo.measurableSet
  have hνS0 : ν S ≠ 0 := hνpos S hSo ⟨b0, hb0S⟩
  have hνSfin : ν S ≠ ⊤ := ne_top_of_le_ne_top hN'fin.ne (measure_mono hSN')
  have hlbS := hlb S hSN hSm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V → ℝ≥0∞, ψ = (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ v)) :=
    ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]
    exact (ENNReal.measurable_ofReal.comp hφc.measurable).indicator (hf'.measurable hSm)
  have hA : ENNReal.ofReal δ * μ (f ⁻¹' (ι '' S) ∩ W) ≤ ∫⁻ v in U, ψ v ∂μ := by
    calc ENNReal.ofReal δ * μ (f ⁻¹' (ι '' S) ∩ W)
        = ∫⁻ v in f ⁻¹' (ι '' S) ∩ W, ENNReal.ofReal δ ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ v in f ⁻¹' (ι '' S) ∩ W, ψ v ∂μ := by
          apply setLIntegral_mono hψm
          intro v hv
          obtain ⟨⟨s, hs, hsv⟩, hvW⟩ := hv
          have hsf : s = f' v := hι (hsv.trans (hff v))
          have hvS : v ∈ f' ⁻¹' S := by
            rw [Set.mem_preimage, ← hsf]
            exact hs
          rw [hψ, Set.indicator_of_mem hvS]
          exact ENNReal.ofReal_le_ofReal (hWφ v hvW)
      _ ≤ ∫⁻ v in U, ψ v ∂μ := lintegral_mono_set (fun v hv => hWU hv.2)
  have hfibψ : ∀ b, ∫⁻ v, ψ v ∂(fib b) ≤ S.indicator (fun _ => ENNReal.ofReal ε) b := by
    intro b
    have hae : ∀ᵐ v ∂(fib b), f' v = b := by
      refine ae_iff.mpr (measure_mono_null ?_ (hsupp b))
      intro v hv hv'
      exact hv (hι ((hff v).symm.trans hv'.1))
    by_cases hbS : b ∈ S
    · rw [Set.indicator_of_mem hbS]
      have heq : ∫⁻ v, ψ v ∂(fib b) = ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
        apply lintegral_congr_ae
        filter_upwards [hae] with v hv
        have hvS : v ∈ f' ⁻¹' S := by
          rw [Set.mem_preimage, hv]
          exact hbS
        rw [hψ, Set.indicator_of_mem hvS]
      rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hint b (Set.mem_univ b))
        (Eventually.of_forall hφ0)]
      exact ENNReal.ofReal_le_ofReal (hSε b hbS).le
    · have heq : ∫⁻ v, ψ v ∂(fib b) = ∫⁻ _v, (0 : ℝ≥0∞) ∂(fib b) := by
        apply lintegral_congr_ae
        filter_upwards [hae] with v hv
        have hvS : v ∉ f' ⁻¹' S := by
          rw [Set.mem_preimage, hv]
          exact hbS
        simp [hψ, hvS]
      rw [heq, lintegral_zero]
      exact bot_le
  have hU : ∫⁻ v in U, ψ v ∂μ ≤ ENNReal.ofReal ε * ν S := by
    rw [hdis ψ hψm]
    calc ∫⁻ b, ∫⁻ v, ψ v ∂(fib b) ∂ν ≤ ∫⁻ b, S.indicator (fun _ => ENNReal.ofReal ε) b ∂ν :=
          lintegral_mono hfibψ
      _ = ENNReal.ofReal ε * ν S := lintegral_indicator_const hSm _
  have hlt : ENNReal.ofReal ε < c * ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal hc', ← ENNReal.ofReal_mul hcr.le,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have := mul_pos hcr hδ
    linarith
  have h0 : ENNReal.ofReal δ * (c * ν S) ≤ ENNReal.ofReal δ * μ (f ⁻¹' (ι '' S) ∩ W) := by
    gcongr
  have h1 : ENNReal.ofReal δ * (c * ν S) ≤ ENNReal.ofReal ε * ν S := h0.trans (hA.trans hU)
  have h2 : ν S * ENNReal.ofReal ε < ν S * (c * ENNReal.ofReal δ) :=
    ENNReal.mul_lt_mul_right hνS0 hνSfin hlt
  have h3 : ENNReal.ofReal δ * (c * ν S) = ν S * (c * ENNReal.ofReal δ) := by ring
  have h4 : ENNReal.ofReal ε * ν S = ν S * ENNReal.ofReal ε := by ring
  rw [h3, h4] at h1
  exact lt_irrefl _ (h1.trans_lt h2)
end PI.VolStabW.LocPosW
