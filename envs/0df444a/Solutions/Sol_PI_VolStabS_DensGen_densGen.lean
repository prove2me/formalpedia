-- Prove2me | solution 1 for PI.VolStabS.DensGen.densGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:16.748628+00:00
-- url     : https://prove2.me/submissions/8e59f85b-6a8d-4730-9a82-e6eb25ecc561

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_DensGen
import Theorems.Thm_PI_VolStabS_DensGen_ae_fib
import Theorems.Thm_PI_VolStabS_DensGen_fib_set
import Theorems.Thm_PI_VolStabS_DensGen_eq_zero_of_setIntegral_c
import Theorems.Thm_PI_VolStabS_DensGen_cut_props

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
namespace PI.VolStabS.DensGen
theorem _root_.solution [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts μ] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {B' N : Set X} (hfib : IsFibreFamily μ f ι U ν B fib)
    {f' : V → X} (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (hNU : ∀ v, f' v ∈ N → v ∈ U)
    {Φ : V → ℂ} (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) {g : X → ℂ}
    (hg : IsContDensityOn μ f ι ν B' Φ g) {b0 : X} (hB : B ∈ 𝓝 b0) (hB' : B' ∈ 𝓝 b0)
    (hN : N ∈ 𝓝 b0) :
    g b0 = ∫ v, Φ v ∂(fib b0) := by
  obtain ⟨C, hCn, hCsub, hCc⟩ := local_compact_nhds (inter_mem (inter_mem hB hB') hN)
  obtain ⟨K, hKn, hKsub, hKc⟩ := local_compact_nhds (interior_mem_nhds.2 hCn)
  obtain ⟨ψ, hψK, hψ0, -, -⟩ := exists_continuous_one_zero_of_isCompact hKc
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.2 hKsub)
  have hKC : K ⊆ C := hKsub.trans interior_subset
  have hKB : K ⊆ B := fun b hb => (hCsub (hKC hb)).1.1
  have hKB' : K ⊆ B' := fun b hb => (hCsub (hKC hb)).1.2
  have hψC : ∀ x, ψ x ≠ 0 → x ∈ C := by
    intro x hx
    by_contra hxC
    exact hx (by simpa using hψ0 (fun hxi => hxC (interior_subset hxi)))
  have hCU : ∀ v, f' v ∈ C → v ∈ U := fun v hv => hNU v (hCsub hv).2
  obtain ⟨hrc, hrs, hrU⟩ := cut_props hf' (fun v => (Φ v).re) (Complex.continuous_re.comp hΦc)
    (hΦs.comp_left (g := Complex.re) Complex.zero_re) ψ ψ.continuous C hCc.isClosed hψC hCU
  obtain ⟨hic, his, hiU⟩ := cut_props hf' (fun v => (Φ v).im) (Complex.continuous_im.comp hΦc)
    (hΦs.comp_left (g := Complex.im) Complex.zero_im) ψ ψ.continuous C hCc.isClosed hψC hCU
  have hr3 := hfib.2.2 _ hrc hrs hrU
  have hi3 := hfib.2.2 _ hic his hiU
  have hcut : ∀ v, f' v ∈ K → Φ v = (((Φ v).re * ψ (f' v) : ℝ) : ℂ) +
      (((Φ v).im * ψ (f' v) : ℝ) : ℂ) * Complex.I := by
    intro v hv
    have h1 : ψ (f' v) = 1 := by simpa using hψK hv
    rw [h1, mul_one, mul_one]
    exact (Complex.re_add_im _).symm
  obtain ⟨H, hH⟩ : ∃ H : X → ℂ, H = fun b => ((∫ v, (Φ v).re * ψ (f' v) ∂(fib b) : ℝ) : ℂ) +
      ((∫ v, (Φ v).im * ψ (f' v) ∂(fib b) : ℝ) : ℂ) * Complex.I := ⟨_, rfl⟩
  have hHc : ContinuousOn H K := by
    rw [hH]
    exact (Complex.continuous_ofReal.comp_continuousOn (hr3.2.mono hKB)).add
      ((Complex.continuous_ofReal.comp_continuousOn (hi3.2.mono hKB)).mul continuousOn_const)

  have hA : ∀ b ∈ K, ∫ v, Φ v ∂(fib b) = H b := by
    intro b hb
    rw [hH]
    have hIr := hr3.1 b (hKB hb)
    have hIi := hi3.1 b (hKB hb)
    rw [integral_congr_ae (g := fun v => (((Φ v).re * ψ (f' v) : ℝ) : ℂ) +
      (((Φ v).im * ψ (f' v) : ℝ) : ℂ) * Complex.I) ?_]
    · rw [integral_add hIr.ofReal (hIi.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
        integral_complex_ofReal]
    · filter_upwards [ae_fib hfib hff' hι b] with v hv
      exact hcut v (hv ▸ hb)

  have hBint : ∀ S, IsCompact S → S ⊆ K → ∫ b in S, g b ∂ν = ∫ b in S, H b ∂ν := by
    intro S hS hSK
    have hAm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
    have hpre : f ⁻¹' (ι '' S) = f' ⁻¹' S := by
      ext v
      simp [hff', hι.mem_set_image]
    rw [← hg.2 S hS (hSK.trans hKB'), hpre,
      setIntegral_congr_fun hAm (fun v hv => hcut v (hSK hv)),
      integral_add (hrc.integrable_of_hasCompactSupport hrs).ofReal.integrableOn.integrable
        ((hic.integrable_of_hasCompactSupport his).ofReal.mul_const _).integrableOn.integrable,
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      fib_set hfib hf' hff' hι _ hrc hrs hrU S hS (hSK.trans hKB),
      fib_set hfib hf' hff' hι _ hic his hiU S hS (hSK.trans hKB), hH,
      integral_add ((hr3.2.mono (hSK.trans hKB)).integrableOn_compact hS).integrable.ofReal
        (((hi3.2.mono (hSK.trans hKB)).integrableOn_compact hS).integrable.ofReal.mul_const _),
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
  have hD := eq_zero_of_setIntegral_c (ν := ν) (fun b => g b - H b) K b0 hKn
    ((hg.1.mono hKB').sub hHc) (fun S hS hSK => by
      rw [integral_sub ((hg.1.mono (hSK.trans hKB')).integrableOn_compact hS)
        ((hHc.mono hSK).integrableOn_compact hS), hBint S hS hSK, sub_self])
  rw [hA b0 (mem_of_mem_nhds hKn)]
  exact sub_eq_zero.1 hD
end PI.VolStabS.DensGen
