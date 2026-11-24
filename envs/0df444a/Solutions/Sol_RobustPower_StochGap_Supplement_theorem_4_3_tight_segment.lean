-- Prove2me | solution 1 for RobustPower.StochGap.Supplement.theorem_4_3_tight_segment
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T03:07:14.227815+00:00
-- url     : https://prove2.me/submissions/23146cd4-bf04-4a82-92c3-4a036ca0917f

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix
namespace RobustPower.StochGap.Supplement

theorem theorem_4_3_tight_segment {Ω : Type*} (b : Ω → Fin 2 → ℝ)
    (hrange : Set.range b = {v : Fin 2 → ℝ | 0 ≤ v ∧ v 0 + v 1 = 1}) :
    RobustPower.StochGap.zRob (0 : Matrix (Fin 2) (Fin 0) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        b ∅ ∅ 0 (fun _ => 1) =
      2 * RobustPower.AdaptGap.zAdapt (0 : Matrix (Fin 2) (Fin 0) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) b 0 (fun _ _ => 1) ∅ ∅ := by
  have hr : ∀ ω, 0 ≤ b ω ∧ b ω 0 + b ω 1 = 1 := fun ω => by
    have h : b ω ∈ Set.range b := ⟨ω, rfl⟩
    rw [hrange] at h; exact h
  have h10 : ∃ ω, b ω = ![1, 0] := by
    have h : (![1, 0] : Fin 2 → ℝ) ∈ {v : Fin 2 → ℝ | 0 ≤ v ∧ v 0 + v 1 = 1} := by
      refine ⟨fun i => ?_, by simp⟩
      fin_cases i <;> simp
    rw [← hrange] at h; exact h
  have h01 : ∃ ω, b ω = ![0, 1] := by
    have h : (![0, 1] : Fin 2 → ℝ) ∈ {v : Fin 2 → ℝ | 0 ≤ v ∧ v 0 + v 1 = 1} := by
      refine ⟨fun i => ?_, by simp⟩
      fin_cases i <;> simp
    rw [← hrange] at h; exact h
  have h2 : ((2:ℝ):EReal) = 2 := by first | rfl | norm_cast | simp
  have hzr : RobustPower.StochGap.zRob (0 : Matrix (Fin 2) (Fin 0) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) b ∅ ∅ 0 (fun _ => 1) = 2 := by
    unfold RobustPower.StochGap.zRob
    apply le_antisymm
    · have hf : RobustPower.StochGap.RobFeasible (0 : Matrix (Fin 2) (Fin 0) ℝ)
          (1 : Matrix (Fin 2) (Fin 2) ℝ) b ∅ ∅ 0 1 := by
        refine ⟨⟨le_refl _, by simp⟩, ⟨zero_le_one, by simp⟩, fun ω => ?_⟩
        intro i
        have := hr ω
        have a0 : 0 ≤ b ω 0 := this.1 0
        have a1 : 0 ≤ b ω 1 := this.1 1
        fin_cases i <;> simp <;> linarith
      refine iInf_le_of_le 0 (iInf_le_of_le 1 (iInf_le_of_le hf ?_))
      have : (0 : Fin 0 → ℝ) ⬝ᵥ 0 + (fun _ : Fin 2 => (1:ℝ)) ⬝ᵥ 1 = 2 := by
        simp [dotProduct]; try norm_num
      rw [this, h2]
    · refine le_iInf fun x => le_iInf fun y => le_iInf fun hf => ?_
      obtain ⟨_, _, hb⟩ := hf
      obtain ⟨ω1, hω1⟩ := h10
      obtain ⟨ω2, hω2⟩ := h01
      have e1 := hb ω1 0
      have e2 := hb ω2 1
      rw [hω1] at e1; rw [hω2] at e2
      simp at e1 e2
      have : (2:ℝ) ≤ 0 ⬝ᵥ x + (fun _ : Fin 2 => (1:ℝ)) ⬝ᵥ y := by
        simp [dotProduct, Fin.sum_univ_two]; linarith
      rw [← h2]; exact EReal.coe_le_coe_iff.mpr this
  have hza : RobustPower.AdaptGap.zAdapt (0 : Matrix (Fin 2) (Fin 0) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) b 0 (fun _ _ => 1) ∅ ∅ = 1 := by
    unfold RobustPower.AdaptGap.zAdapt RobustPower.AdaptGap.adaptCost
    apply le_antisymm
    · have hf : RobustPower.AdaptGap.AdaptFeasible (0 : Matrix (Fin 2) (Fin 0) ℝ)
          (1 : Matrix (Fin 2) (Fin 2) ℝ) b ∅ ∅ 0 b :=
        ⟨⟨le_refl _, by simp⟩, fun ω => ⟨⟨(hr ω).1, by simp⟩, by simp⟩⟩
      refine iInf_le_of_le 0 (iInf_le_of_le b (iInf_le_of_le hf ?_))
      simp only [dotProduct_zero, EReal.coe_zero, zero_add]
      refine iSup_le fun ω => ?_
      have : (fun _ : Fin 2 => (1:ℝ)) ⬝ᵥ b ω = 1 := by
        simp [dotProduct, Fin.sum_univ_two, (hr ω).2]
      rw [this]; norm_num
    · refine le_iInf fun x => le_iInf fun y => le_iInf fun hf => ?_
      obtain ⟨ω1, -⟩ := h10
      simp only [zero_dotProduct, EReal.coe_zero, zero_add]
      refine le_iSup_of_le ω1 ?_
      have h := (hf.2 ω1).2
      have e0 := h 0
      have e1 := h 1
      simp at e0 e1
      have : (1:ℝ) ≤ (fun _ : Fin 2 => (1:ℝ)) ⬝ᵥ y ω1 := by
        simp [dotProduct, Fin.sum_univ_two]; linarith [(hr ω1).2]
      exact_mod_cast this
  rw [hzr, hza, mul_one]

end RobustPower.StochGap.Supplement

open RobustPower.StochGap.Supplement in
theorem solution {Ω : Type*} (b : Ω → Fin 2 → ℝ)
    (hrange : Set.range b = {v : Fin 2 → ℝ | 0 ≤ v ∧ v 0 + v 1 = 1}) :
    RobustPower.StochGap.zRob (0 : Matrix (Fin 2) (Fin 0) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        b ∅ ∅ 0 (fun _ => 1) =
      2 * RobustPower.AdaptGap.zAdapt (0 : Matrix (Fin 2) (Fin 0) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) b 0 (fun _ _ => 1) ∅ ∅ :=
  RobustPower.StochGap.Supplement.theorem_4_3_tight_segment b hrange
