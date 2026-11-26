-- Prove2me | solution 1 for RamseyLib.card_offDiag_sym2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:16:01.625671+00:00
-- url     : https://prove2.me/submissions/3c879958-683d-477e-a66e-8e745477e753

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib
namespace RamseyLib
theorem _root_.solution {α : Type*} [DecidableEq α] (S : Finset α) :
    (S.sym2.filter (fun e => ¬ e.IsDiag)).card = S.card.choose 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := S.sym2) (p := Sym2.IsDiag)
  have hd : S.sym2.filter Sym2.IsDiag = S.image Sym2.diag := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, -⟩, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨c, hc, hce⟩
        rw [Sym2.diag, Sym2.eq_iff] at hce
        rcases hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨⟨hc, hc⟩, rfl⟩
  have hc : (S.card + 1).choose 2 = S.card + S.card.choose 2 := by
    rw [Nat.choose_succ_left _ _ (by norm_num)]; simp
  rw [hd, Finset.card_image_of_injective _ Sym2.diag_injective, Finset.card_sym2, hc] at h
  omega
end RamseyLib
