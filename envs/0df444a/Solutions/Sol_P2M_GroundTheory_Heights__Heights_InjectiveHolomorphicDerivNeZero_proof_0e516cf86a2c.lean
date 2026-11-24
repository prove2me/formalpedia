-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InjectiveHolomorphicDerivNeZero_proof_0e516cf86a2c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:42.443938+00:00
-- url     : https://prove2.me/submissions/f70b81d1-b31b-4538-9eb1-b8fb317b472a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicDerivNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicDerivNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace InjectiveHolomorphicDerivNeZero
theorem _root_.solution : InjectiveHolomorphicDerivNeZero.Statement := by
  intro D f hD hf hinj a ha hder
  have hDa : D ∈ 𝓝 a := hD.mem_nhds ha
  set g : ℂ → ℂ := fun z ↦ f z - f a with hg
  have hga : AnalyticAt ℂ g a := (hf.analyticAt hDa).sub analyticAt_const

  have hntop : analyticOrderAt g a ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hev : ∀ᶠ z in 𝓝[≠] a, (g z = 0 ∧ z ∈ D) ∧ z ∈ ({a}ᶜ : Set ℂ) :=
      ((htop.and (hDa : ∀ᶠ z in 𝓝 a, z ∈ D)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hz0, hzD⟩, hza⟩ := hev.exists
    exact hza (hinj hzD ha (sub_eq_zero.mp hz0))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
  obtain ⟨u, hu, hua, hfac⟩ := hga.analyticOrderAt_eq_natCast.mp hn.symm
  simp only [smul_eq_mul] at hfac
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfac.self_of_nhds
    simp [hg] at this
    exact hua this.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd : HasDerivAt (fun z ↦ (z - a) ^ 1 * u z) (u a) a := by
      have := ((hasDerivAt_id' a).sub_const a).mul hu.differentiableAt.hasDerivAt
      simp only [pow_one]
      exact this.congr_deriv (by simp)
    have : deriv g a = u a :=
      (EventuallyEq.deriv_eq (hfac : g =ᶠ[𝓝 a] fun z ↦ (z - a) ^ 1 * u z)).trans hd.deriv
    rw [hg, deriv_sub_const, hder] at this
    exact hua this.symm

  set c : ℂ := u a ^ ((n : ℂ)⁻¹) with hc
  set v : ℂ → ℂ := fun z ↦ c * (u z / u a) ^ ((n : ℂ)⁻¹) with hv
  have hva : AnalyticAt ℂ v a := analyticAt_const.mul
    ((hu.div analyticAt_const hua).cpow analyticAt_const (by simp [hua, Complex.one_mem_slitPlane]))
  have hvpow : ∀ z, v z ^ n = u z := by
    intro z
    rw [hv, mul_pow, hc, Complex.cpow_nat_inv_pow _ hn0, Complex.cpow_nat_inv_pow _ hn0]
    field_simp
  have hv0 : v a ≠ 0 := by
    intro h
    have := hvpow a
    rw [h, zero_pow hn0] at this
    exact hua this.symm
  set w : ℂ → ℂ := fun z ↦ (z - a) * v z with hw
  have hwd : HasDerivAt w (v a) a := by
    have := ((hasDerivAt_id' a).sub_const a).mul hva.differentiableAt.hasDerivAt
    exact this.congr_deriv (by simp)
  have hwa : w a = 0 := by simp [hw]
  have hgw : ∀ z, g z = (z - a) ^ n * u z → g z = w z ^ n := by
    intro z hz
    rw [hz, ← hvpow z, ← mul_pow]

  have hmap : 𝓝 (w a) ≤ map w (𝓝 a) := by
    have hwan : AnalyticAt ℂ w a := (analyticAt_id.sub analyticAt_const).mul hva
    refine hwan.eventually_constant_or_nhds_le_map_nhds.resolve_left ?_
    intro hconst
    have h1 : deriv w a = 0 := by
      rw [EventuallyEq.deriv_eq (hconst : w =ᶠ[𝓝 a] fun _ ↦ w a)]
      simp
    exact hv0 (hwd.deriv.symm.trans h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hmap (image_mem_map (inter_mem hDa hfac)))
  rw [hwa] at hball
  have hk : 1 < n := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht
  have htn : ‖t‖ = ε / 2 := by rw [ht, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at htn
    linarith
  obtain ⟨z₁, ⟨hz₁D, hz₁⟩, hw₁⟩ := hball (by
    rw [Metric.mem_ball, dist_zero_right, htn]; linarith)
  obtain ⟨z₂, ⟨hz₂D, hz₂⟩, hw₂⟩ := hball (show ζ * t ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hprim.norm'_eq_one hn0, htn]; linarith)
  have hg₁ := hgw z₁ hz₁
  have hg₂ := hgw z₂ hz₂
  rw [hw₁] at hg₁
  rw [hw₂, mul_pow, hprim.pow_eq_one, one_mul] at hg₂
  have hf12 : f z₁ = f z₂ := by
    have : g z₁ = g z₂ := hg₁.trans hg₂.symm
    simpa [hg] using this
  have h12 := hinj hz₁D hz₂D hf12
  rw [h12, hw₂] at hw₁
  have : (ζ - 1) * t = 0 := by rw [sub_mul, one_mul, hw₁, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact hprim.ne_one hk (sub_eq_zero.mp h)
  · exact ht0 h
end InjectiveHolomorphicDerivNeZero
end GroundTheory.Heights₂.Heights
