-- Prove2me | solution 1 for UnderstandingML.separable_iff_margin_one
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:53:59.672518+00:00
-- url     : https://prove2.me/submissions/76eda01a-1202-47b5-a9c7-1a9fcf13c145

import Definitions.Def_UnderstandingML_Linear

open MeasureTheory
open scoped InnerProductSpace

open UnderstandingML in
theorem solution {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) :
    Separable x y ↔ ∃ w : Vec d, ∀ i, 1 ≤ y i * ⟪w, x i⟫_ℝ := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(∑ j, (y j * ⟪w, x j⟫_ℝ)⁻¹) • w, fun i => ?_⟩
    have hpos : ∀ j, 0 ≤ (y j * ⟪w, x j⟫_ℝ)⁻¹ := fun j => (inv_pos.2 (hw j)).le
    have hle : (y i * ⟪w, x i⟫_ℝ)⁻¹ ≤ ∑ j, (y j * ⟪w, x j⟫_ℝ)⁻¹ :=
      Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ i)
    rw [inner_smul_left]
    simp only [RCLike.conj_to_real]
    have hi := hw i
    calc (1 : ℝ) = (y i * ⟪w, x i⟫_ℝ)⁻¹ * (y i * ⟪w, x i⟫_ℝ) := (inv_mul_cancel₀ hi.ne').symm
      _ ≤ (∑ j, (y j * ⟪w, x j⟫_ℝ)⁻¹) * (y i * ⟪w, x i⟫_ℝ) :=
          mul_le_mul_of_nonneg_right hle hi.le
      _ = y i * ((∑ j, (y j * ⟪w, x j⟫_ℝ)⁻¹) * ⟪w, x i⟫_ℝ) := by ring
  · rintro ⟨w, hw⟩
    exact ⟨w, fun i => lt_of_lt_of_le one_pos (hw i)⟩
