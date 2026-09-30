-- Prove2me | solution 1 for UnderstandingML.hard_svm_max_margin
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:13:04.215986+00:00
-- url     : https://prove2.me/submissions/491916c6-f448-4523-adee-e802b296a135

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : ∃ i j, y i = 1 ∧ y j = -1) (w₀ : Vec d) (b₀ : ℝ)
    (h : IsHardSVM x y w₀ b₀) :
    w₀ ≠ 0 ∧ ‖‖w₀‖⁻¹ • w₀‖ = 1 ∧
    ∀ (w : Vec d) (b : ℝ), ‖w‖ = 1 →
      sampleMargin x y w b ≤ sampleMargin x y (‖w₀‖⁻¹ • w₀) (b₀ / ‖w₀‖) := by
  obtain ⟨i₀, j₀, hi₀, hj₀⟩ := hboth
  have : Nonempty (Fin m) := ⟨i₀⟩
  have hw₀ : w₀ ≠ 0 := by
    rintro rfl
    have h1 := h.1 i₀
    have h2 := h.1 j₀
    simp only [inner_zero_left, zero_add, hi₀, hj₀] at h1 h2
    linarith
  have hn : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
  refine ⟨hw₀, norm_smul_inv_norm hw₀, ?_⟩
  -- the normalized margin is at least `‖w₀‖⁻¹`
  have hnorm : ‖w₀‖⁻¹ ≤ sampleMargin x y (‖w₀‖⁻¹ • w₀) (b₀ / ‖w₀‖) := by
    apply le_ciInf
    intro i
    have := h.1 i
    have e : y i * (⟪‖w₀‖⁻¹ • w₀, x i⟫_ℝ + b₀ / ‖w₀‖) =
        ‖w₀‖⁻¹ * (y i * (⟪w₀, x i⟫_ℝ + b₀)) := by
      rw [real_inner_smul_left]; field_simp
    rw [e]
    have hinv : 0 < ‖w₀‖⁻¹ := inv_pos.mpr hn
    nlinarith
  intro w b hw
  set γ := sampleMargin x y w b with hγ
  rcases le_or_gt γ 0 with hle | hpos
  · exact le_trans hle (le_trans (inv_pos.mpr hn).le hnorm)
  · refine le_trans ?_ hnorm
    have hbdd : BddBelow (Set.range fun i => y i * (⟪w, x i⟫_ℝ + b)) :=
      (Set.finite_range _).bddBelow
    have hγi : ∀ i, γ ≤ y i * (⟪w, x i⟫_ℝ + b) := fun i => ciInf_le hbdd i
    have hfeas : ∀ i, 1 ≤ y i * (⟪γ⁻¹ • w, x i⟫_ℝ + γ⁻¹ * b) := by
      intro i
      have e : y i * (⟪γ⁻¹ • w, x i⟫_ℝ + γ⁻¹ * b) = γ⁻¹ * (y i * (⟪w, x i⟫_ℝ + b)) := by
        rw [real_inner_smul_left]; ring
      rw [e, ← div_eq_inv_mul, le_div_iff₀ hpos, one_mul]
      exact hγi i
    have := h.2 _ _ hfeas
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)] at this
    rw [le_inv_comm₀ hpos hn]
    exact this
