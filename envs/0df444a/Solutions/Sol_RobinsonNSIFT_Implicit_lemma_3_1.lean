-- Prove2me | solution 1 for RobinsonNSIFT.Implicit.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:56:40.40733+00:00
-- url     : https://prove2.me/submissions/627aad96-0d16-49e4-ab78-93866e928e36

import Mathlib
import Definitions.Def_RobinsonNSIFT_Implicit_Basic

set_option autoImplicit false
open Set Metric
open scoped NNReal
open RobinsonNSIFT.Implicit

theorem rob_lemma_3_1 {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set X) (hΩ : IsOpen Ω) (f h : X → Y) (η : ℝ≥0) (hh : LipschitzOnWith η h Ω)
    (x₀ : X) (hx₀ : x₀ ∈ Ω) (y₀ : Y) (hfx₀ : f x₀ = y₀) (α δ : ℝ)
    (hδ : ExpansionAtLeast f Ω δ)
    (h1 : closedBall y₀ α ⊆ f '' Ω)
    (h2 : (η : ℝ) < δ)
    (h3 : closedBall x₀ (α / δ) ⊆ Ω)
    (h4 : 0 ≤ (1 - η / δ) * α - ‖h x₀‖) :
    closedBall y₀ ((1 - η / δ) * α - ‖h x₀‖) ⊆ (f + h) '' closedBall x₀ (α / δ) ∧
      ExpansionAtLeast (f + h) Ω (δ - η) ∧ 0 < δ - η := by
  have hη0 : (0 : ℝ) ≤ η := η.coe_nonneg
  have hδpos : 0 < δ := lt_of_le_of_lt hη0 h2
  haveI : Nonempty X := ⟨x₀⟩
  have hα0 : 0 ≤ α / δ := by
    have hpos : 0 < 1 - η / δ := by
      have := (div_lt_one hδpos).mpr h2
      linarith
    have : 0 ≤ α := by
      by_contra hneg
      push_neg at hneg
      nlinarith [norm_nonneg (h x₀), mul_neg_of_pos_of_neg hpos hneg]
    positivity
  refine ⟨?_, ?_, by linarith⟩
  · intro y hy
    rw [mem_closedBall] at hy
    set B : Set X := closedBall x₀ (α / δ) with hB
    set g : X → X := fun x => Function.invFunOn f Ω (y - h x) with hg
    -- key facts
    have hzmem : ∀ x ∈ B, y - h x ∈ closedBall y₀ α := by
      intro x hxB
      rw [mem_closedBall] at hxB ⊢
      have hxΩ : x ∈ Ω := h3 hxB
      have hlip := hh.dist_le_mul x hxΩ x₀ hx₀
      have e1 : dist (y - h x) y₀ ≤ dist y y₀ + dist (h x) (h x₀) + ‖h x₀‖ := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
        have : y - h x - y₀ = (y - y₀) - (h x - h x₀) - h x₀ := by abel
        rw [this]
        calc ‖(y - y₀) - (h x - h x₀) - h x₀‖ ≤ ‖(y - y₀) - (h x - h x₀)‖ + ‖h x₀‖ := norm_sub_le _ _
          _ ≤ ‖y - y₀‖ + ‖h x - h x₀‖ + ‖h x₀‖ := by gcongr; exact norm_sub_le _ _
      have e2 : (η : ℝ) * dist x x₀ ≤ η * (α / δ) := mul_le_mul_of_nonneg_left hxB hη0
      have e3 : (η : ℝ) * (α / δ) = η / δ * α := by ring
      nlinarith
    have hgx : ∀ x ∈ B, g x ∈ Ω ∧ f (g x) = y - h x := by
      intro x hxB
      obtain ⟨a, ha, hfa⟩ := h1 (hzmem x hxB)
      exact Function.invFunOn_pos ⟨a, ha, hfa⟩
    have hmaps : Set.MapsTo g B B := by
      intro x hxB
      obtain ⟨hgΩ, hgf⟩ := hgx x hxB
      have := hδ _ hgΩ x₀ hx₀
      rw [hgf, hfx₀] at this
      have h5 : dist (y - h x) y₀ ≤ α := mem_closedBall.mp (hzmem x hxB)
      rw [hB, mem_closedBall, le_div_iff₀ hδpos]
      linarith
    have hK : ((Real.toNNReal ((η : ℝ) / δ) : ℝ≥0) : ℝ) = η / δ :=
      Real.coe_toNNReal _ (div_nonneg hη0 hδpos.le)
    have hKlt : Real.toNNReal ((η : ℝ) / δ) < 1 := by
      rw [← NNReal.coe_lt_coe, hK]
      simpa using (div_lt_one hδpos).mpr h2
    have hcontr : ContractingWith (Real.toNNReal ((η : ℝ) / δ)) (hmaps.restrict g B B) := by
      refine ⟨hKlt, LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
      obtain ⟨hgΩ, hgf⟩ := hgx x.1 x.2
      obtain ⟨hgΩ', hgf'⟩ := hgx x'.1 x'.2
      have := hδ _ hgΩ _ hgΩ'
      rw [hgf, hgf'] at this
      have e1 : dist (y - h x.1) (y - h x'.1) = dist (h x.1) (h x'.1) := by
        exact dist_sub_left _ _ _
      have e2 := hh.dist_le_mul x.1 (h3 x.2) x'.1 (h3 x'.2)
      rw [hK]
      simp only [MapsTo.restrict, Subtype.dist_eq]
      show dist (g x.1) (g x'.1) ≤ η / δ * dist x.1 x'.1
      rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
      nlinarith
    have hBc : IsComplete B := (isClosed_closedBall).isComplete
    obtain ⟨x, hxB, hfix, -⟩ := hcontr.exists_fixedPoint' hBc hmaps (x := x₀)
      (mem_closedBall_self hα0) (edist_ne_top _ _)
    refine ⟨x, hxB, ?_⟩
    obtain ⟨-, hgf⟩ := hgx x hxB
    have : g x = x := hfix
    rw [this] at hgf
    simp only [Pi.add_apply, hgf]
    abel
  · intro x₁ hx₁ x₂ hx₂
    have := hδ x₁ hx₁ x₂ hx₂
    have e2 := hh.dist_le_mul x₁ hx₁ x₂ hx₂
    have e3 : dist (f x₁) (f x₂) ≤ dist ((f + h) x₁) ((f + h) x₂) + dist (h x₁) (h x₂) := by
      simp only [Pi.add_apply]
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
      calc ‖f x₁ - f x₂‖ = ‖(f x₁ + h x₁ - (f x₂ + h x₂)) - (h x₁ - h x₂)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    nlinarith

theorem solution {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set X) (hΩ : IsOpen Ω) (f h : X → Y) (η : ℝ≥0) (hh : LipschitzOnWith η h Ω)
    (x₀ : X) (hx₀ : x₀ ∈ Ω) (y₀ : Y) (hfx₀ : f x₀ = y₀) (α δ : ℝ)
    (hδ : ExpansionAtLeast f Ω δ)
    (h1 : closedBall y₀ α ⊆ f '' Ω)
    (h2 : (η : ℝ) < δ)
    (h3 : closedBall x₀ (α / δ) ⊆ Ω)
    (h4 : 0 ≤ (1 - η / δ) * α - ‖h x₀‖) :
    closedBall y₀ ((1 - η / δ) * α - ‖h x₀‖) ⊆ (f + h) '' closedBall x₀ (α / δ) ∧
      ExpansionAtLeast (f + h) Ω (δ - η) ∧ 0 < δ - η :=
  rob_lemma_3_1 Ω hΩ f h η hh x₀ hx₀ y₀ hfx₀ α δ hδ h1 h2 h3 h4
