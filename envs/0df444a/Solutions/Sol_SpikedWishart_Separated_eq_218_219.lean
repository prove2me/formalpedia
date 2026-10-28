-- Prove2me | solution 1 for SpikedWishart.Separated.eq_218_219
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:45:17.180376+00:00
-- url     : https://prove2.me/submissions/c19267fe-ff28-46b3-be4f-78b7eddb943d

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Phase

namespace Aux_SW_218

open SpikedWishart.Separated

lemma hasDeriv1 (γ π₁ q : ℝ) (z : ℂ) (h1 : z ∈ Complex.slitPlane) (h2 : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (fPhase γ π₁ q)
      (-((mu γ π₁ : ℝ) : ℂ) + z⁻¹ + ((γ⁻¹ ^ 2 : ℝ) : ℂ) * (1 - z)⁻¹) z := by
  have t1 : HasDerivAt (fun z : ℂ => -((mu γ π₁ : ℝ) : ℂ) * (z - q)) (-((mu γ π₁ : ℝ) : ℂ) * 1) z :=
    ((hasDerivAt_id z).sub_const (q : ℂ)).const_mul _
  have t2 := Complex.hasDerivAt_log h1
  have t3 : HasDerivAt (fun z : ℂ => Complex.log (1 - z)) ((1 - z)⁻¹ * (-1)) z :=
    (Complex.hasDerivAt_log h2).comp z ((hasDerivAt_id z).const_sub 1)
  have := (t1.add t2).sub (t3.const_mul ((γ⁻¹ ^ 2 : ℝ) : ℂ))
  refine this.congr_deriv ?_
  ring

lemma hasDeriv2 (γ π₁ : ℝ) (z : ℂ) (h1 : z ≠ 0) (h2 : 1 - z ≠ 0) :
    HasDerivAt (fun z : ℂ => -((mu γ π₁ : ℝ) : ℂ) + z⁻¹ + ((γ⁻¹ ^ 2 : ℝ) : ℂ) * (1 - z)⁻¹)
      (-(z ^ 2)⁻¹ + ((γ⁻¹ ^ 2 : ℝ) : ℂ) * ((1 - z) ^ 2)⁻¹) z := by
  have t2 := hasDerivAt_inv h1
  have t3 : HasDerivAt (fun z : ℂ => (1 - z)⁻¹) (-((1 - z) ^ 2)⁻¹ * (-1)) z :=
    (hasDerivAt_inv h2).comp z ((hasDerivAt_id z).const_sub 1)
  have := ((hasDerivAt_const z (-((mu γ π₁ : ℝ) : ℂ))).add t2).add
    (t3.const_mul ((γ⁻¹ ^ 2 : ℝ) : ℂ))
  refine this.congr_deriv ?_
  ring

lemma second (γ π₁ q x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    deriv (fPhase γ π₁ q) (x : ℂ) = ((-(mu γ π₁) + x⁻¹ + γ⁻¹ ^ 2 * (1 - x)⁻¹ : ℝ) : ℂ) ∧
    deriv (deriv (fPhase γ π₁ q)) (x : ℂ) =
      ((-(x ^ 2)⁻¹ + γ⁻¹ ^ 2 * ((1 - x) ^ 2)⁻¹ : ℝ) : ℂ) := by
  set U : Set ℂ := {z | z ∈ Complex.slitPlane ∧ 1 - z ∈ Complex.slitPlane} with hU
  have hUo : IsOpen U :=
    Complex.isOpen_slitPlane.inter
      (Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id))
  have hxU : (x : ℂ) ∈ U := by
    refine ⟨Complex.ofReal_mem_slitPlane.mpr hx0, ?_⟩
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith)
  have hev : deriv (fPhase γ π₁ q) =ᶠ[nhds (x : ℂ)]
      (fun z : ℂ => -((mu γ π₁ : ℝ) : ℂ) + z⁻¹ + ((γ⁻¹ ^ 2 : ℝ) : ℂ) * (1 - z)⁻¹) := by
    filter_upwards [hUo.mem_nhds hxU] with z hz
    exact (hasDeriv1 γ π₁ q z hz.1 hz.2).deriv
  refine ⟨?_, ?_⟩
  · rw [(hasDeriv1 γ π₁ q _ hxU.1 hxU.2).deriv]
    push_cast; ring
  · rw [hev.deriv_eq]
    have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have hx1' : 1 - (x : ℂ) ≠ 0 := by
      rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by linarith : (1 - x) ≠ 0)
    rw [(hasDeriv2 γ π₁ _ hx0' hx1').deriv]
    push_cast; ring

end Aux_SW_218

open SpikedWishart.Separated Aux_SW_218 in
theorem solution (γ π₁ q : ℝ) (hγ : 1 ≤ γ) (hπ : 0 < π₁) (h209 : 1 + γ⁻¹ < π₁⁻¹) :
    deriv (fPhase γ π₁ q) (π₁ : ℂ) = 0 ∧
    deriv (fPhase γ π₁ q) ((1 / (mu γ π₁ * π₁) : ℝ) : ℂ) = 0 ∧
    π₁ < γ / (1 + γ) ∧ γ / (1 + γ) < 1 / (mu γ π₁ * π₁) ∧ 1 / (mu γ π₁ * π₁) < 1 ∧
    deriv (deriv (fPhase γ π₁ q)) (π₁ : ℂ) = -((nu γ π₁ : ℝ) : ℂ) ^ 2 ∧ -(nu γ π₁) ^ 2 < 0 ∧
    deriv (deriv (fPhase γ π₁ q)) ((1 / (mu γ π₁ * π₁) : ℝ) : ℂ) =
      ((γ * nu γ π₁ * mu γ π₁ * π₁ * (1 - π₁) : ℝ) : ℂ) ^ 2 ∧
    0 < (γ * nu γ π₁ * mu γ π₁ * π₁ * (1 - π₁)) ^ 2 := by
  have hγ0 : 0 < γ := by linarith
  -- basic real facts
  have hkey : π₁ * (1 + γ) < γ := by
    have h := mul_lt_mul_of_pos_right h209 hπ
    rw [inv_mul_cancel₀ hπ.ne'] at h
    have h2 := mul_lt_mul_of_pos_right h hγ0
    have : (1 + γ⁻¹) * π₁ * γ = π₁ * (1 + γ) := by field_simp; ring
    linarith
  have hp1 : π₁ < 1 := by nlinarith
  have h1p : 0 < 1 - π₁ := by linarith
  set c := γ⁻¹ ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hcγ : c * γ ^ 2 = 1 := by rw [hc]; field_simp
  have hmu : mu γ π₁ = 1 / π₁ + c / (1 - π₁) := rfl
  have hmup : mu γ π₁ * π₁ = 1 + c * π₁ / (1 - π₁) := by
    rw [hmu]; field_simp
  have hmp1 : 1 < mu γ π₁ * π₁ := by
    rw [hmup]; have : 0 < c * π₁ / (1 - π₁) := by positivity
    linarith
  have hmu0 : 0 < mu γ π₁ := by rw [hmu]; positivity
  -- ν² positive
  have hpγ : π₁ / γ < 1 - π₁ := by
    rw [div_lt_iff₀ hγ0]; nlinarith
  have hνsq_pos : 0 < 1 / π₁ ^ 2 - c / (1 - π₁) ^ 2 := by
    have h1 : c * π₁ ^ 2 = (π₁ / γ) ^ 2 := by rw [hc]; field_simp
    have h2 : (π₁ / γ) ^ 2 < (1 - π₁) ^ 2 := by
      have : 0 < π₁ / γ := by positivity
      nlinarith
    rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hν2 : nu γ π₁ ^ 2 = 1 / π₁ ^ 2 - c / (1 - π₁) ^ 2 := by
    unfold nu; rw [Real.sq_sqrt hνsq_pos.le]
  have hν0 : 0 < nu γ π₁ := by unfold nu; exact Real.sqrt_pos.mpr hνsq_pos
  -- the second point
  set w := 1 / (mu γ π₁ * π₁) with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw1 : w < 1 := by rw [hw, div_lt_one (by linarith)]; exact hmp1
  obtain ⟨dp1, dp2⟩ := second γ π₁ q π₁ hπ hp1
  obtain ⟨dw1, dw2⟩ := second γ π₁ q w hw0 hw1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dp1, hmu]
    have : -(1 / π₁ + c / (1 - π₁)) + π₁⁻¹ + c * (1 - π₁)⁻¹ = 0 := by ring
    rw [← hc, this]; simp
  · rw [dw1]
    have : -mu γ π₁ + w⁻¹ + c * (1 - w)⁻¹ = 0 := by
      have hm1 : mu γ π₁ * π₁ - 1 = c * π₁ / (1 - π₁) := by rw [hmup]; ring
      have hwinv : w⁻¹ = mu γ π₁ * π₁ := by rw [hw]; simp
      have h1w : 1 - w = (mu γ π₁ * π₁ - 1) / (mu γ π₁ * π₁) := by
        rw [hw]; field_simp
      rw [hwinv, h1w, hm1]
      field_simp
      rw [hmu]
      field_simp
      ring
    rw [← hc, this]; simp
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_div_iff₀ (by linarith) (by linarith), one_mul]
    rw [hmup]
    have : c * π₁ / (1 - π₁) * γ < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one h1p]
      have : c * π₁ * γ = π₁ / γ := by rw [hc]; field_simp
      rw [this]; exact hpγ
    nlinarith
  · exact hw1
  · rw [dp2]
    have : -(π₁ ^ 2)⁻¹ + c * ((1 - π₁) ^ 2)⁻¹ = -(nu γ π₁ ^ 2) := by
      rw [hν2]; ring
    rw [← hc, this]; push_cast; ring
  · nlinarith
  · rw [dw2]
    have : -(w ^ 2)⁻¹ + c * ((1 - w) ^ 2)⁻¹ =
        (γ * nu γ π₁ * mu γ π₁ * π₁ * (1 - π₁)) ^ 2 := by
      have hm1 : mu γ π₁ * π₁ - 1 = c * π₁ / (1 - π₁) := by rw [hmup]; ring
      have hwinv : w⁻¹ = mu γ π₁ * π₁ := by rw [hw]; simp
      have h1w : 1 - w = (mu γ π₁ * π₁ - 1) / (mu γ π₁ * π₁) := by
        rw [hw]; field_simp
      have hγc : γ ^ 2 = 1 / c := by field_simp; linarith
      have e1 : -(w ^ 2)⁻¹ + c * ((1 - w) ^ 2)⁻¹ =
          (mu γ π₁ * π₁) ^ 2 * ((1 - π₁) ^ 2 / (c * π₁ ^ 2) - 1) := by
        rw [← inv_pow, hwinv, h1w, hm1]
        have hM : mu γ π₁ * π₁ ≠ 0 := by positivity
        field_simp
        ring
      have e2 : (γ * nu γ π₁ * mu γ π₁ * π₁ * (1 - π₁)) ^ 2 =
          (mu γ π₁ * π₁) ^ 2 * ((1 - π₁) ^ 2 / (c * π₁ ^ 2) - 1) := by
        have : (γ * nu γ π₁ * mu γ π₁ * π₁ * (1 - π₁)) ^ 2 =
            γ ^ 2 * nu γ π₁ ^ 2 * (mu γ π₁ * π₁) ^ 2 * (1 - π₁) ^ 2 := by ring
        rw [this, hν2, hγc]
        field_simp <;> ring
      rw [e1, e2]
    rw [← hc, this]; push_cast; ring
  · positivity
