-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.compact_iff_complemented
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:16:17.068003+00:00
-- url     : https://prove2.me/submissions/00049c1a-b42b-47ad-bb4d-da8b93e093a1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem solution (L : Type u) [Order.Frame L]
    (hL : IsStoneLocale L) (a : L) :
    IsCompactElement a ↔ ∃ b : L, IsCompl a b := by
  classical
  constructor
  · intro ha
    rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at ha
    have hreg := hL.2 a
    obtain ⟨t, hts, hat⟩ := ha {b : L | bᶜ ⊔ a = ⊤} (le_of_eq hreg)
    have key : ∀ t : Finset L, (↑t ⊆ {b : L | bᶜ ⊔ a = ⊤}) → (t.sup id)ᶜ ⊔ a = ⊤ := by
      intro t
      induction t using Finset.induction_on with
      | empty => intro _; simp
      | insert x t hx ih =>
        intro hsub
        rw [Finset.sup_insert, id, compl_sup, sup_inf_right,
          hsub (Finset.mem_insert_self x t),
          ih (fun y hy => hsub (Finset.mem_insert_of_mem hy)), inf_top_eq]
    refine ⟨(t.sup id)ᶜ, ?_, ?_⟩
    · rw [disjoint_iff]
      apply le_antisymm _ bot_le
      calc a ⊓ (t.sup id)ᶜ ≤ t.sup id ⊓ (t.sup id)ᶜ := inf_le_inf_right _ hat
        _ = ⊥ := inf_compl_self _
    · rw [codisjoint_iff, sup_comm]; exact key t hts
  · rintro ⟨b, hab⟩
    rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup]
    intro s hs
    have htop := hL.1.1
    rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at htop
    have h1 : (⊤ : L) ≤ sSup (insert b s) := by
      rw [← hab.sup_eq_top, sSup_insert]
      exact sup_comm a b ▸ sup_le_sup_left hs b
    obtain ⟨t, hts, htt⟩ := htop _ h1
    refine ⟨t.erase b, ?_, ?_⟩
    · intro x hx
      have hx' := Finset.mem_erase.1 hx
      rcases hts hx'.2 with h | h
      · exact absurd h hx'.1
      · exact h
    · have h2 : t.sup id ≤ b ⊔ (t.erase b).sup id := by
        apply Finset.sup_le
        intro x hx
        by_cases hxb : x = b
        · subst hxb; exact le_sup_left
        · exact le_sup_of_le_right (Finset.le_sup (f := id) (Finset.mem_erase.2 ⟨hxb, hx⟩))
      calc a = a ⊓ ⊤ := (inf_top_eq a).symm
        _ ≤ a ⊓ (b ⊔ (t.erase b).sup id) := inf_le_inf_left _ (htt.trans h2)
        _ = (a ⊓ b) ⊔ (a ⊓ (t.erase b).sup id) := inf_sup_left _ _ _
        _ = a ⊓ (t.erase b).sup id := by rw [hab.inf_eq_bot, bot_sup_eq]
        _ ≤ (t.erase b).sup id := inf_le_right
