-- Prove2me | solution 1 for SqrtAgreement.SRA.agree_ge_sq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:43:47.743331+00:00
-- url     : https://prove2.me/submissions/0192afb9-96c4-4830-9553-08221bd21482

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

open Finset

open SqrtAgreement.SRA in
theorem solution {m k : ℕ} (G : GenModel m k) (α : ℝ) (hG : G.Valid) (hα : 0 < α)
    (hsep : G.AlphaSeparated α) : ∀ y : Fin k, α ^ 2 ≤ G.agree y := by
  obtain ⟨hPX0, hPX1, hp0, hp1⟩ := hG
  intro y
  have hne : ((Finset.univ : Finset (Fin k)).offDiag).Nonempty := by
    by_contra h
    unfold GenModel.AlphaSeparated GenModel.delta at hsep
    rw [dif_neg h] at hsep
    linarith
  obtain ⟨⟨y1, y2⟩, hp⟩ := hne
  rw [mem_offDiag] at hp
  obtain ⟨y', hy'⟩ : ∃ y', y ≠ y' := by
    by_cases h : y = y1
    · exact ⟨y2, h ▸ hp.2.2⟩
    · exact ⟨y1, h⟩
  have hne' : ((Finset.univ : Finset (Fin k)).offDiag).Nonempty := ⟨_, mem_offDiag.mpr hp⟩
  have hgap : α ≤ G.csGap y y' := by
    refine hsep.trans ?_
    unfold GenModel.delta
    rw [dif_pos hne']
    have hm : (y, y') ∈ (Finset.univ : Finset (Fin k)).offDiag :=
      mem_offDiag.mpr ⟨mem_univ y, mem_univ y', hy'⟩
    have := Finset.inf'_le (s := (Finset.univ : Finset (Fin k)).offDiag)
      (fun yy : Fin k × Fin k => G.csGap yy.1 yy.2) hm
    exact this
  have hin : 0 ≤ ∑ x, G.PX x * G.p x y * G.p x y' :=
    sum_nonneg (fun x _ => mul_nonneg (mul_nonneg (hPX0 x) (hp0 x y)) (hp0 x y'))
  have ha0 : ∀ z, 0 ≤ G.agree z := fun z =>
    sum_nonneg (fun x _ => mul_nonneg (hPX0 x) (sq_nonneg _))
  have ha1 : G.agree y' ≤ 1 := by
    unfold GenModel.agree
    rw [← hPX1]
    apply sum_le_sum
    intro x _
    have hle : G.p x y' ≤ 1 := by
      rw [← hp1 x]
      exact single_le_sum (fun z _ => hp0 x z) (mem_univ y')
    have : G.p x y' ^ 2 ≤ 1 := by nlinarith [hp0 x y']
    nlinarith [hPX0 x]
  have hsq : α ≤ Real.sqrt (G.agree y * G.agree y') := by
    unfold GenModel.csGap at hgap
    linarith
  have h2 : α ^ 2 ≤ G.agree y * G.agree y' := by
    have := pow_le_pow_left₀ hα.le hsq 2
    rwa [Real.sq_sqrt (mul_nonneg (ha0 y) (ha0 y'))] at this
  nlinarith [ha0 y]
