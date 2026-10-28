-- Prove2me | solution 2 for RobinsonNSIFT.Implicit.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:26:46.017916+00:00
-- url     : https://prove2.me/submissions/81ae741d-972e-4577-974e-26b4e043701d

import Mathlib
import Definitions.Def_RobinsonNSIFT_Implicit_Basic
import Theorems.Thm_RobinsonNSIFT_Implicit_eq_3_1_3_2

-- carved verbatim out of submission 447e6204-10e5-4f38-bea9-6fcfc1f1b703, lines 192-266

section
set_option autoImplicit false
open Set Filter Topology Metric
open scoped NNReal
open RobinsonNSIFT.Implicit

theorem solution {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (x₀ : X) (y₀ : Y) (Ξ : Set X) (H : Set Y) (hΞ : Ξ ∈ 𝓝 x₀) (hH : H ∈ 𝓝 y₀)
    (F : X → Y → Z) (hF₀ : F x₀ y₀ = 0) (f : X → Z) (hf₀ : f x₀ = 0)
    (ha : StronglyApproxInX f F x₀ y₀)
    (φ : ℝ≥0) (hb : ∀ x ∈ Ξ, LipschitzOnWith φ (F x) H)
    (hc : f '' Ξ ∈ 𝓝 (0 : Z))
    (d₀ : ℝ) (hd₀ : 0 < d₀) (hd : ExpansionAtLeast f Ξ d₀)
    (lam : ℝ≥0) (hlam : (φ : ℝ) / d₀ < lam) :
    ∃ U ∈ 𝓝 x₀, ∃ V ∈ 𝓝 y₀, U ⊆ Ξ ∧ V ⊆ H ∧ ∃ x : Y → X, Set.MapsTo x V U ∧
      x y₀ = x₀ ∧ LipschitzOnWith lam x V ∧
      ∀ y ∈ V, F (x y) y = 0 ∧ ∀ x' ∈ U, F x' y = 0 → x' = x y := by
  have hφ0 : (0 : ℝ) ≤ φ := φ.coe_nonneg
  have hlam0 : (0 : ℝ) < lam := lt_of_le_of_lt (div_nonneg hφ0 hd₀.le) hlam
  have hlamd : (φ : ℝ) < lam * d₀ := by
    rw [div_lt_iff₀ hd₀] at hlam; exact hlam
  set ε : ℝ := (lam * d₀ - φ) / (2 * lam) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have hεd : ε < d₀ := by
    rw [hε, div_lt_iff₀ (by linarith)]; nlinarith
  have hde : (φ : ℝ) ≤ lam * (d₀ - ε) := by
    have : lam * (d₀ - ε) = (lam * d₀ + φ) / 2 := by
      rw [hε]; field_simp; ring
    rw [this]; linarith
  have hde0 : 0 < d₀ - ε := by linarith
  obtain ⟨α, hα, κ, hκ, V, hV, hVH, hball, hmain⟩ :=
    RobinsonNSIFT.Implicit.eq_3_1_3_2 x₀ y₀ Ξ H hΞ hH F hF₀ f hf₀ ha φ hb hc d₀ hd₀ hd ε hε0 hεd
  set U : Set X := closedBall x₀ (α / d₀) with hU
  have hUn : U ∈ 𝓝 x₀ := closedBall_mem_nhds _ (by positivity)
  have hex : ∀ y ∈ V, ∃ x' ∈ U, F x' y = 0 := by
    intro y hy
    obtain ⟨-, hcov, hθ⟩ := hmain y hy
    have : (0 : Z) ∈ closedBall (0 : Z) ((1 - ε / d₀) * α - ‖F x₀ y‖) := by
      rw [mem_closedBall, dist_self]; linarith
    obtain ⟨x', hx', hFx'⟩ := hcov this
    exact ⟨x', hx', hFx'⟩
  have hinj : ∀ y ∈ V, ∀ x₁ ∈ U, ∀ x₂ ∈ U, F x₁ y = 0 → F x₂ y = 0 → x₁ = x₂ := by
    intro y hy x₁ hx₁ x₂ hx₂ h1 h2
    have := (hmain y hy).1 x₁ hx₁ x₂ hx₂
    simp only [h1, h2, dist_self] at this
    have : dist x₁ x₂ ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_pos hde0 hcon]
    exact dist_le_zero.mp this
  classical
  let xf : Y → X := fun y => if h : y ∈ V then Classical.choose (hex y h) else x₀
  have hxf : ∀ y (h : y ∈ V), xf y ∈ U ∧ F (xf y) y = 0 := by
    intro y h
    have := Classical.choose_spec (hex y h)
    simpa [xf, h] using this
  have hy₀V : y₀ ∈ V := mem_of_mem_nhds hV
  have hx₀U : x₀ ∈ U := mem_closedBall_self (by positivity)
  refine ⟨U, hUn, V, hV, fun x hx => (hball hx), hVH, xf, fun y hy => (hxf y hy).1, ?_, ?_, ?_⟩
  · exact (hinj y₀ hy₀V _ (hxf y₀ hy₀V).1 _ hx₀U (hxf y₀ hy₀V).2 hF₀)
  · refine LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ => ?_
    obtain ⟨hx1, hf1⟩ := hxf y₁ hy₁
    obtain ⟨hx2, hf2⟩ := hxf y₂ hy₂
    have h1 := (hmain y₁ hy₁).1 _ hx1 _ hx2
    have h2 := (hb _ (hball hx2)).dist_le_mul y₂ (hVH hy₂) y₁ (hVH hy₁)
    beta_reduce at h1
    rw [hf1] at h1
    rw [hf2] at h2
    have h5 : (d₀ - ε) * dist (xf y₁) (xf y₂) ≤ φ * dist y₂ y₁ := by
      linarith
    have h6 : (d₀ - ε) * dist (xf y₁) (xf y₂) ≤ (d₀ - ε) * (lam * dist y₁ y₂) := by
      calc (d₀ - ε) * dist (xf y₁) (xf y₂) ≤ φ * dist y₂ y₁ := h5
        _ ≤ lam * (d₀ - ε) * dist y₁ y₂ := by
          rw [dist_comm y₂ y₁]; exact mul_le_mul_of_nonneg_right hde dist_nonneg
        _ = (d₀ - ε) * (lam * dist y₁ y₂) := by ring
    exact le_of_mul_le_mul_left h6 hde0
  · intro y hy
    refine ⟨(hxf y hy).2, fun x' hx' hFx' => ?_⟩
    exact hinj y hy x' hx' _ (hxf y hy).1 hFx' (hxf y hy).2

end
