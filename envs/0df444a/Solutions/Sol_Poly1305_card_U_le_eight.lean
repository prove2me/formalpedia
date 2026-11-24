-- Prove2me | solution 1 for Poly1305.card_U_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:03:36.712552+00:00
-- url     : https://prove2.me/submissions/87b0803b-62c0-4ef4-bbba-c85f85b5d050

import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Definitions.Def_Poly1305Bernstein

section
section
namespace Poly1305.HashPart

theorem leVal_lt (s : Str16) : leVal s < 2 ^ 128 := by
  unfold leVal
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h := fun j : Fin 16 => (s j).isLt
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  have h8 := h 8; have h9 := h 9; have h10 := h 10; have h11 := h 11
  have h12 := h 12; have h13 := h 13; have h14 := h 14; have h15 := h 15
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at *
  norm_num at *
  omega

theorem card_U_le_eight_dev (g : Str16) :
    ((Finset.Icc (-(2 ^ 130 - 6 : ℤ)) (2 ^ 130 - 6)).filter
      (fun x => x ≡ (leVal g : ℤ) [ZMOD 2 ^ 128])).card ≤ 8 := by
  have hg := leVal_lt g
  have hsub : (Finset.Icc (-(2 ^ 130 - 6 : ℤ)) (2 ^ 130 - 6)).filter
      (fun x => x ≡ (leVal g : ℤ) [ZMOD 2 ^ 128]) ⊆
      (Finset.Icc (-4 : ℤ) 3).image (fun k => (leVal g : ℤ) + 2 ^ 128 * k) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hlo, hhi⟩, hmod⟩ := hx
    obtain ⟨k, hk⟩ := (Int.ModEq.dvd hmod.symm)
    rw [Finset.mem_image]
    refine ⟨k, ?_, by omega⟩
    rw [Finset.mem_Icc]
    have hg' : ((leVal g : ℕ) : ℤ) < 2 ^ 128 := by exact_mod_cast hg
    have hg0 : (0 : ℤ) ≤ ((leVal g : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((leVal g : ℕ) : ℤ) = G at *
    norm_num at hlo hhi hk hg'
    omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.Icc (-4 : ℤ) 3).card := Finset.card_image_le
    _ = 8 := by rfl

end Poly1305.HashPart

end
end

section
open Poly1305

theorem solution (g : Str16) :
    ((Finset.Icc (-(2 ^ 130 - 6 : ℤ)) (2 ^ 130 - 6)).filter
      (fun x => x ≡ (leVal g : ℤ) [ZMOD 2 ^ 128])).card ≤ 8 := by
  apply Poly1305.HashPart.card_U_le_eight_dev <;> assumption

end
