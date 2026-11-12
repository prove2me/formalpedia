-- Prove2me | solution 1 for avram_jb22_original_stopped_two_noise_integrable_cen_pointwise_upper_bound_abe809fc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:35:19.977206+00:00
-- url     : https://prove2.me/submissions/b234aa11-6134-4d27-b7f1-244b7153c8b1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb22_original_stopped_two_noise_dominated_mesh_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : ℕ → Finset ι)
    (R J : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (hJint : ∀ u : ℝ≥0, Integrable (J u) P)
    (hJmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (J v) ω = J u ω)
    (a b : ℕ → ι → ℝ≥0)
    (WG WJ : ℕ → ι → Ω → ℝ)
    (hab : ∀ k, ∀ i ∈ S k, a k i ≤ b k i)
    (hWG : ∀ k, ∀ i ∈ S k,
      Measurable[𝓕.rightCont (a k i)] (WG k i))
    (hWJ : ∀ k, ∀ i ∈ S k,
      Measurable[𝓕.rightCont (a k i)] (WJ k i))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hGprod : ∀ k, ∀ i ∈ S k,
      Integrable (fun ω =>
        (if τ ω ≤ a k i then 0 else WG k i ω) *
          (R (b k i) ω - R (a k i) ω)) P)
    (hJprod : ∀ k, ∀ i ∈ S k,
      Integrable (fun ω =>
        (if τ ω ≤ a k i then 0 else WJ k i ω) *
          (J (b k i) ω - J (a k i) ω)) P)
    (Gseq Jseq : ℕ → Ω → ℝ)
    (hGsource : ∀ k ω, Gseq k ω =
      ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WG k i ω) *
        (R (b k i) ω - R (a k i) ω))
    (hJsource : ∀ k ω, Jseq k ω =
      ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WJ k i ω) *
        (J (b k i) ω - J (a k i) ω))
    (MG MJ BG BJ : Ω → ℝ)
    (hGconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => Gseq k ω) atTop (𝓝 (MG ω)))
    (hJconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => Jseq k ω) atTop (𝓝 (MJ ω)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖Gseq k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖Jseq k ω‖ ≤ BJ ω)
    (hMGAE : AEStronglyMeasurable MG P)
    (hMJAE : AEStronglyMeasurable MJ P) 
    (hGdomall : ∀ᵐ ω ∂P, ∀ k, ‖Gseq k ω‖ ≤ BG ω)
    (hJdomall : ∀ᵐ ω ∂P, ∀ k, ‖Jseq k ω‖ ≤ BJ ω)
    : ∀ᵐ ω ∂P, ‖MG ω‖ ≤ ‖BG ω‖ := by
    filter_upwards [hGconv, hGdomall] with ω hc hd
    have hlim : ‖MG ω‖ ≤ BG ω :=
      le_of_tendsto hc.norm (Filter.Eventually.of_forall hd)
    exact hlim.trans (by simpa only [Real.norm_eq_abs] using
      (le_abs_self (BG ω)))
end
