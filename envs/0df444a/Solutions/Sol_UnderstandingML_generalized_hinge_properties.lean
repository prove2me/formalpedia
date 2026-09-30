-- Prove2me | solution 1 for UnderstandingML.generalized_hinge_properties
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T06:40:55.142985+00:00
-- url     : https://prove2.me/submissions/b45f910d-91df-4355-9b35-0655c9245bde

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d : ℕ} {X Y : Type*} [Fintype Y] [Nonempty Y]
    (Δ : Y → Y → ℝ) (Ψ : X → Y → Vec d) (w : Vec d) (z : X × Y) :
    (∀ h : X → Y, IsArgmaxPredictor Ψ w h → Δ (h z.1) z.2 ≤ genHingeLoss Δ Ψ w z) ∧
    ((∀ y', 0 ≤ Δ y' z.2) → Δ z.2 z.2 = 0 →
      (∀ y', y' ≠ z.2 → ⟪w, Ψ z.1 y'⟫_ℝ + Δ y' z.2 ≤ ⟪w, Ψ z.1 z.2⟫_ℝ) →
      ∀ h : X → Y, IsArgmaxPredictor Ψ w h → genHingeLoss Δ Ψ w z = Δ (h z.1) z.2) ∧
    ConvexOn ℝ Set.univ (fun w ↦ genHingeLoss Δ Ψ w z) ∧
    ∀ w₁ w₂ : Vec d, |genHingeLoss Δ Ψ w₁ z - genHingeLoss Δ Ψ w₂ z| ≤
      (⨆ y' : Y, ‖Ψ z.1 y' - Ψ z.1 z.2‖) * ‖w₁ - w₂‖ := by
  obtain ⟨x, y⟩ := z
  simp only
  -- every term of the maximum is below the generalized hinge loss
  have hle : ∀ (v : Vec d) (y' : Y),
      Δ y' y + ⟪v, Ψ x y' - Ψ x y⟫_ℝ ≤ genHingeLoss Δ Ψ v (x, y) := fun v y' ↦
    le_ciSup (Finite.bddAbove_range (fun y' ↦ Δ y' y + ⟪v, Ψ x y' - Ψ x y⟫_ℝ)) y'
  -- the generalized hinge loss is the least upper bound of the terms
  have hsup : ∀ (v : Vec d) (c : ℝ), (∀ y', Δ y' y + ⟪v, Ψ x y' - Ψ x y⟫_ℝ ≤ c) →
      genHingeLoss Δ Ψ v (x, y) ≤ c := fun v c hc ↦ ciSup_le hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- upper bound: take `y' = h x`
    intro h hh
    refine le_trans ?_ (hle w (h x))
    have := hh x y
    rw [inner_sub_right]
    linarith
  · -- tightness under the margin condition
    intro hΔ hΔ0 hmargin h hh
    have hzero : genHingeLoss Δ Ψ w (x, y) = 0 := by
      apply le_antisymm
      · apply hsup
        intro y'
        rw [inner_sub_right]
        by_cases hy : y' = y
        · subst hy; simp [hΔ0]
        · have := hmargin y' hy; linarith
      · have := hle w y
        simpa [hΔ0] using this
    rw [hzero]
    by_cases hy : h x = y
    · rw [hy, hΔ0]
    · have h1 := hmargin (h x) hy
      have h2 := hh x y
      have h3 := hΔ (h x)
      linarith
  · -- convexity: a maximum of affine functions
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
    apply hsup
    intro y'
    have hu := hle u y'
    have hv := hle v y'
    have e : Δ y' y + ⟪a • u + b • v, Ψ x y' - Ψ x y⟫_ℝ =
        a * (Δ y' y + ⟪u, Ψ x y' - Ψ x y⟫_ℝ) + b * (Δ y' y + ⟪v, Ψ x y' - Ψ x y⟫_ℝ) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have : Δ y' y = (a + b) * Δ y' y := by rw [hab, one_mul]
      linarith [this]
    rw [e, smul_eq_mul, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
  · -- Lipschitz bound: Cauchy–Schwarz on every term
    intro w₁ w₂
    set R := ⨆ y' : Y, ‖Ψ x y' - Ψ x y‖
    have hR : ∀ y', ‖Ψ x y' - Ψ x y‖ ≤ R := fun y' ↦
      le_ciSup (Finite.bddAbove_range (fun y' ↦ ‖Ψ x y' - Ψ x y‖)) y'
    have key : ∀ u v : Vec d, genHingeLoss Δ Ψ u (x, y) ≤
        genHingeLoss Δ Ψ v (x, y) + R * ‖u - v‖ := by
      intro u v
      apply hsup
      intro y'
      have h1 := hle v y'
      have h2 : ⟪u - v, Ψ x y' - Ψ x y⟫_ℝ ≤ R * ‖u - v‖ := by
        calc ⟪u - v, Ψ x y' - Ψ x y⟫_ℝ ≤ ‖u - v‖ * ‖Ψ x y' - Ψ x y‖ := real_inner_le_norm _ _
          _ ≤ ‖u - v‖ * R := mul_le_mul_of_nonneg_left (hR y') (norm_nonneg _)
          _ = R * ‖u - v‖ := mul_comm _ _
      have e : ⟪u, Ψ x y' - Ψ x y⟫_ℝ = ⟪v, Ψ x y' - Ψ x y⟫_ℝ + ⟪u - v, Ψ x y' - Ψ x y⟫_ℝ := by
        rw [inner_sub_left]; ring
      linarith
    rw [abs_sub_le_iff]
    constructor
    · linarith [key w₁ w₂]
    · have := key w₂ w₁
      rw [norm_sub_rev] at this
      linarith
