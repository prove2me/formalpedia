-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.nullIff_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:50.231142+00:00
-- url     : https://prove2.me/submissions/c6d10b14-67d5-4a78-a362-7d7c9cfeb84d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_mom_add
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_mom_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_mom_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_ell_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_mom_ellpow
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_strip_open
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_strip_conn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution (hS : SecLine) (hP : PowSpan) : NullIff := by
  intro m n ε c t hc ht P
  constructor
  · intro hN b hb
    obtain ⟨δ, hδ, hd, hre, hder⟩ := hS m n ε c t hc P b hb
    set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ,
      evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF
    have hball : Metric.ball (0:ℂ) δ ⊆ {z : ℂ | |z.im| < δ} := by
      intro z hz
      simp only [Metric.mem_ball, dist_zero_right] at hz
      exact lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
    have hzero : ∀ k, iteratedDeriv k F 0 = 0 := by
      intro k
      rw [hder k, ← mom_ellpow, hN _ (Subalgebra.pow_mem _ (ell_mem ε b) k), mul_zero]
    have hloc : F =ᶠ[𝓝 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) hδ] with z hz
      rw [← Complex.taylorSeries_eq_on_ball' hz (hd.mono hball)]
      simp [hzero]
    have han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := hd.analyticOnNhd (strip_open δ)
    have h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
    have h1 : (1:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
    have hF1 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (strip_conn δ) h0 hloc h1
    have e1 := hre 1 (by simp)
    rw [one_smul] at e1
    rw [← e1]
    exact hF1
  · intro hall R hR
    have hR' : R ∈ Submodule.span ℂ {R : PX m n | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ),
        b.IsHermitian ∧ R = (∑ i : Fin n, ∑ j : Fin n, C (b i j) * Qp ε j i) ^ k} := by
      rw [← hP m n ε]
      exact hR
    clear hR
    induction hR' using Submodule.span_induction with
    | mem R hmem =>
      obtain ⟨b, k, hb, rfl⟩ := hmem
      obtain ⟨δ, hδ, hd, hre, hder⟩ := hS m n ε c t hc P b hb
      set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ,
        evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF
      have han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := hd.analyticOnNhd (strip_open δ)
      have h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
      have hreal : ∀ r : ℝ, F r = 0 := by
        intro r
        rw [show F r = _ from hre (r:ℂ) (Complex.ofReal_im r)]
        apply hall
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_smul, hb.eq, Complex.star_def, Complex.conj_ofReal]
      have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), F z = 0 := by
        have hc0 : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 0) (𝓝 0) := by
          simpa using Complex.continuous_ofReal.tendsto (0:ℝ)
        have hT : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hc0.mono_left nhdsWithin_le_nhds) ?_
          filter_upwards [self_mem_nhdsWithin] with r hr
          simpa using hr
        exact hT.frequently (Frequently.of_forall hreal)
      have hloc := ((han 0 h0).frequently_zero_iff_eventually_zero).mp hfreq
      have hk := hder k
      rw [Filter.EventuallyEq.iteratedDeriv_eq k (hloc : F =ᶠ[𝓝 0] 0)] at hk
      simp at hk
      rw [mom_ellpow]
      exact hk.resolve_left (fun h => ht h.1)
    | zero => exact mom_zero c P
    | add x y _ _ hx hy => rw [mom_add hc, hx, hy, add_zero]
    | smul a x _ hx => rw [mom_smul, hx, mul_zero]
end PositivityTheory.Rg.Sw.FFTSteps
