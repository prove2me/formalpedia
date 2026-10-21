-- Prove2me | solution 1 for PDScenRed.Mean.lossL_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:15:40.473879+00:00
-- url     : https://prove2.me/submissions/907036d2-ffe1-413c-978b-5d4e30948150

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting

set_option autoImplicit false
open scoped InnerProductSpace
open MeasureTheory PDScenRed.Mean

theorem solution {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun ζ => lossL (polytope P qv) zsel ξ ζ) := by
  set Z := polytope P qv with hZ
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hbd : ∀ c : EuclideanSpace ℝ (Fin d), BddAbove ((fun w => ⟪c, w⟫_ℝ) '' Z) := by
    intro c
    refine ⟨‖c‖ * R, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    calc ⟪c, w⟫_ℝ ≤ ‖c‖ * ‖w‖ := real_inner_le_norm _ _
      _ ≤ ‖c‖ * R := by gcongr; exact hR w hw
  have hxi : ∀ c₁ c₂ : EuclideanSpace ℝ (Fin d), ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      SmartPTO.Fisher.xi Z (a • c₁ + b • c₂) ≤ a * SmartPTO.Fisher.xi Z c₁ + b * SmartPTO.Fisher.xi Z c₂ := by
    intro c₁ c₂ a b ha hb hab
    unfold SmartPTO.Fisher.xi
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨w, hw, rfl⟩
    simp only [inner_add_left, inner_smul_left, conj_trivial]
    have h1 : ⟪c₁, w⟫_ℝ ≤ sSup ((fun w => ⟪c₁, w⟫_ℝ) '' Z) := le_csSup (hbd c₁) ⟨w, hw, rfl⟩
    have h2 : ⟪c₂, w⟫_ℝ ≤ sSup ((fun w => ⟪c₂, w⟫_ℝ) '' Z) := le_csSup (hbd c₂) ⟨w, hw, rfl⟩
    nlinarith
  have hg : ConvexOn ℝ Set.univ (fun ζ : EuclideanSpace ℝ (Fin d) => SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • ζ)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have e : ξ - (2 : ℝ) • (a • x + b • y) = a • (ξ - (2 : ℝ) • x) + b • (ξ - (2 : ℝ) • y) := by
      have : ξ = (a + b) • ξ := by rw [hab, one_smul]
      conv_lhs => rw [this]
      simp only [smul_sub, smul_add, add_smul, smul_smul]
      module
    simp only [smul_eq_mul]
    rw [e]
    exact hxi _ _ a b ha hb hab
  have hlin : ConvexOn ℝ Set.univ (fun ζ : EuclideanSpace ℝ (Fin d) => ⟪zsel ξ, ζ⟫_ℝ) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp [inner_add_right, inner_smul_right]
  have h1 : ConvexOn ℝ Set.univ (fun ζ : EuclideanSpace ℝ (Fin d) => max (SmartPTO.Fisher.xi Z (ξ - (2 : ℝ) • ζ)) 0) :=
    hg.sup (convexOn_const 0 convex_univ)
  have h2 : ConvexOn ℝ Set.univ (fun ζ : EuclideanSpace ℝ (Fin d) => max ⟪zsel ξ, ζ⟫_ℝ 0) :=
    hlin.sup (convexOn_const 0 convex_univ)
  have h3 := h1.add (h2.smul (by norm_num : (0:ℝ) ≤ 2))
  exact h3
