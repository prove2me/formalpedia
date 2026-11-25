-- Prove2me | solution 1 for PI.VolStabSW.DensGen.densGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:48.724106+00:00
-- url     : https://prove2.me/submissions/d9d0f117-ec54-44f1-a768-dc2693f43640

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Theorems.Thm_PI_VolStabSW_DensGen_ae_fib
import Theorems.Thm_PI_VolStabSW_DensGen_fib_set
import Theorems.Thm_PI_VolStabSW_DensGen_eq_zero_of_setIntegral_c
import Theorems.Thm_PI_VolStabSW_DensGen_cut_props

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
theorem _root_.solution [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts μ] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {B' N : Set X} (hfib : IsFibreFamily μ f ι U ν B fib)
    {f' : V → X} (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (hNU : ∀ v, f' v ∈ N → v ∈ U)
    {Φ : V → ℂ} (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) {g : X → ℂ}
    (hg : IsContDensityOn μ f ι ν B' Φ g) {b0 : X} (hB : B ∈ 𝓝 b0) (hB' : B' ∈ 𝓝 b0)
    (hN : N ∈ 𝓝 b0) :
    g b0 = ∫ v, Φ v ∂(fib b0) := by
  classical
  obtain ⟨M, hM, hMN, hMc⟩ := local_compact_nhds hN
  obtain ⟨K, hK, hKM, hKc⟩ := local_compact_nhds (interior_mem_nhds.mpr hM)
  obtain ⟨ψ, hψ1, hψ0, -, -⟩ := exists_continuous_one_zero_of_isCompact hKc
    isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hKM)
  have hψC : ∀ x, ψ x ≠ 0 → x ∈ M := by
    intro x hx
    by_contra hxM
    exact hx (hψ0 (fun hxi => hxM (interior_subset hxi)))
  have hCU : ∀ v, f' v ∈ M → v ∈ U := fun v hv => hNU v (hMN hv)
  obtain ⟨hcr, hsr, hur⟩ := cut_props hf' (fun v => (Φ v).re) (Complex.continuous_re.comp hΦc)
    (hΦs.comp_left Complex.zero_re) ψ ψ.continuous M hMc.isClosed hψC hCU
  obtain ⟨hci, hsi, hui⟩ := cut_props hf' (fun v => (Φ v).im) (Complex.continuous_im.comp hΦc)
    (hΦs.comp_left Complex.zero_im) ψ ψ.continuous M hMc.isClosed hψC hCU
  obtain ⟨hintr, hGr⟩ := hfib.2.2 _ hcr hsr hur
  obtain ⟨hinti, hGi⟩ := hfib.2.2 _ hci hsi hui
  have hre : ∀ v, (Φ v * (ψ (f' v) : ℂ)).re = (Φ v).re * ψ (f' v) := fun v => by simp
  have him : ∀ v, (Φ v * (ψ (f' v) : ℂ)).im = (Φ v).im * ψ (f' v) := fun v => by simp
  have hintc : ∀ b ∈ B, Integrable (fun v => Φ v * (ψ (f' v) : ℂ)) (fib b) := by
    intro b hb
    refine Integrable.re_im_iff.mp ⟨?_, ?_⟩
    · exact (hintr b hb).congr (Filter.Eventually.of_forall fun v => by
        simp only [RCLike.re_to_complex, hre])
    · exact (hinti b hb).congr (Filter.Eventually.of_forall fun v => by
        simp only [RCLike.im_to_complex, him])
  have hHeq : ∀ b ∈ B, (∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) =
      ((∫ v, (Φ v).re * ψ (f' v) ∂(fib b) : ℝ) : ℂ) +
        ((∫ v, (Φ v).im * ψ (f' v) ∂(fib b) : ℝ) : ℂ) * Complex.I := by
    intro b hb
    apply Complex.ext
    · have h1 := integral_re (hintc b hb)
      simp only [RCLike.re_to_complex, hre] at h1
      simp [← h1]
    · have h1 := integral_im (hintc b hb)
      simp only [RCLike.im_to_complex, him] at h1
      simp [← h1]
  have hHc : ContinuousOn (fun b => ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) B := by
    refine ContinuousOn.congr (f := fun b => ((∫ v, (Φ v).re * ψ (f' v) ∂(fib b) : ℝ) : ℂ) +
      ((∫ v, (Φ v).im * ψ (f' v) ∂(fib b) : ℝ) : ℂ) * Complex.I) ?_ (fun b hb => hHeq b hb)
    exact (Complex.continuous_ofReal.comp_continuousOn hGr).add
      ((Complex.continuous_ofReal.comp_continuousOn hGi).mul continuousOn_const)
  have hΦint : Integrable (fun v => Φ v * (ψ (f' v) : ℂ)) μ :=
    (hΦc.mul (Complex.continuous_ofReal.comp (ψ.continuous.comp hf'))).integrable_of_hasCompactSupport
      hΦs.mul_right
  have hW : B ∩ B' ∩ K ∈ 𝓝 b0 := Filter.inter_mem (Filter.inter_mem hB hB') hK
  have hDc : ContinuousOn (fun b => g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) (B ∩ B' ∩ K) :=
    (hg.1.mono fun x hx => hx.1.2).sub (hHc.mono fun x hx => hx.1.1)
  have h0 : ∀ S, IsCompact S → S ⊆ B ∩ B' ∩ K →
      ∫ b in S, (g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) ∂ν = 0 := by
    intro S hS hSW
    have hSB : S ⊆ B := fun x hx => (hSW hx).1.1
    have hSB' : S ⊆ B' := fun x hx => (hSW hx).1.2
    have hSK : S ⊆ K := fun x hx => (hSW hx).2
    have hSm : MeasurableSet S := hS.isClosed.measurableSet
    have hS'm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
    have hpre : f ⁻¹' (ι '' S) = f' ⁻¹' S := by
      ext v
      simp only [Set.mem_preimage, Set.mem_image, hff' v]
      constructor
      · rintro ⟨b, hb, hbv⟩
        rw [hι hbv] at hb
        exact hb
      · intro hv
        exact ⟨f' v, hv, rfl⟩
    have hgS := hg.2 S hS hSB'
    rw [hpre] at hgS
    have hcut : ∫ v in f' ⁻¹' S, Φ v ∂μ = ∫ v in f' ⁻¹' S, Φ v * (ψ (f' v) : ℂ) ∂μ := by
      refine setIntegral_congr_fun hS'm (fun v hv => ?_)
      simp only [hψ1 (hSK hv), Pi.one_apply, Complex.ofReal_one, mul_one]
    have hr := fib_set hfib hf' hff' hι _ hcr hsr hur S hS hSB
    have hi := fib_set hfib hf' hff' hι _ hci hsi hui S hS hSB
    have hintS : IntegrableOn (fun b => ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) S ν :=
      (hHc.mono hSB).integrableOn_compact hS
    have hfib_eq : ∫ v in f' ⁻¹' S, Φ v * (ψ (f' v) : ℂ) ∂μ =
        ∫ b in S, (∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) ∂ν := by
      apply Complex.ext
      · have h1 := integral_re (hΦint.integrableOn (s := f' ⁻¹' S))
        have h2 := integral_re hintS
        simp only [RCLike.re_to_complex] at h1 h2
        rw [← h1, ← h2]
        simp only [hre]
        rw [hr]
        refine setIntegral_congr_fun hSm (fun b hb => ?_)
        have h3 := integral_re (hintc b (hSB hb))
        simp only [RCLike.re_to_complex, hre] at h3
        exact h3
      · have h1 := integral_im (hΦint.integrableOn (s := f' ⁻¹' S))
        have h2 := integral_im hintS
        simp only [RCLike.im_to_complex] at h1 h2
        rw [← h1, ← h2]
        simp only [him]
        rw [hi]
        refine setIntegral_congr_fun hSm (fun b hb => ?_)
        have h3 := integral_im (hintc b (hSB hb))
        simp only [RCLike.im_to_complex, him] at h3
        exact h3
    rw [integral_sub ((hg.1.mono hSB').integrableOn_compact hS) hintS, ← hgS, hcut, hfib_eq, sub_self]
  have hD0 := eq_zero_of_setIntegral_c (ν := ν)
    (fun b => g b - ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b)) (B ∩ B' ∩ K) b0 hW hDc h0
  have hb0K : b0 ∈ K := mem_of_mem_nhds hK
  have hfin : ∫ v, Φ v * (ψ (f' v) : ℂ) ∂(fib b0) = ∫ v, Φ v ∂(fib b0) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_fib hfib hff' hι b0] with v hv
    simp only [hv, hψ1 hb0K, Pi.one_apply, Complex.ofReal_one, mul_one]
  rw [← hfin]
  exact sub_eq_zero.mp hD0
end PI.VolStabSW.DensGen
