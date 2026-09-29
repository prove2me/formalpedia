-- Prove2me | solution 1 for Subgroup.exists_int_forall_finsum_ite_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0372d7d8-4406-552b-a9e7-d5c2d92a6273

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_exists_int_forall_finsum_ite_eq_one

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

namespace ArtIndMob

variable {α : Type} [DecidableEq α]

lemma exists_int_sum_eq_one_aux (S : α → Finset α) (card : α → ℕ)
    (hS : ∀ a b, b ∈ S a → b ≠ a → card a < card b) (n₀ : ℕ) (hn₀ : ∀ a, card a < n₀) :
    ∀ k : ℕ, ∃ f : α → ℤ, ∀ a, a ∈ S a → n₀ ≤ card a + k → ∑ b ∈ S a, f b = 1
  | 0 => ⟨0, fun a _ h => absurd h (by have := hn₀ a; omega)⟩
  | k + 1 => by
    obtain ⟨f, hf⟩ := exists_int_sum_eq_one_aux S card hS n₀ hn₀ k
    refine ⟨fun b => if card b + k + 1 = n₀ then 1 - ∑ c ∈ (S b).erase b, f c else f b, ?_⟩
    intro a ha hk
    by_cases hbig : n₀ ≤ card a + k
    · refine (Finset.sum_congr rfl fun b hb => ?_).trans (hf a ha hbig)
      have hne : card b + k + 1 ≠ n₀ := by
        rcases eq_or_ne b a with rfl | hba
        · omega
        · have := hS a b hb hba; omega
      dsimp only
      rw [if_neg hne]
    · have hlev : card a + k + 1 = n₀ := by omega
      rw [← Finset.add_sum_erase _ _ ha, if_pos hlev]
      have hrest : ∑ x ∈ (S a).erase a,
            (if card x + k + 1 = n₀ then 1 - ∑ c ∈ (S x).erase x, f c else f x)
          = ∑ x ∈ (S a).erase a, f x := by
        refine Finset.sum_congr rfl fun b hb => ?_
        obtain ⟨hba, hb'⟩ := Finset.mem_erase.mp hb
        have := hS a b hb' hba
        rw [if_neg (by omega)]
      rw [hrest]; ring

lemma exists_int_sum_eq_one [Fintype α] (S : α → Finset α) (card : α → ℕ)
    (hS : ∀ a b, b ∈ S a → b ≠ a → card a < card b) :
    ∃ f : α → ℤ, ∀ a, a ∈ S a → ∑ b ∈ S a, f b = 1 := by
  obtain ⟨f, hf⟩ := exists_int_sum_eq_one_aux S card hS (Finset.univ.sup card + 1)
    (fun a => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))) (Finset.univ.sup card + 1)
  exact ⟨f, fun a ha => hf a ha (by omega)⟩

end ArtIndMob

theorem solution (p : ℕ) {G : Type} [Group G] [Finite G] :
    ∃ b : Subgroup G → ℤ, ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D then b D else 0) = 1 := by
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  have hlt : ∀ {H D : Subgroup G}, H ≤ D → D ≠ H → Nat.card H < Nat.card D :=
    fun hle hne => lt_of_not_ge fun hge => hne (Subgroup.eq_of_le_of_card_ge hle hge).symm
  obtain ⟨f, hf⟩ := ArtIndMob.exists_int_sum_eq_one
    (fun H : Subgroup G =>
      Finset.univ.filter fun D => IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D)
    (fun D => Nat.card D)
    (by
      intro H D hD hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
      exact hlt hD.2.2 hne)
  refine ⟨f, fun H hc hp => ?_⟩
  have h1 := hf H (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hc, hp, le_rfl⟩)
  rw [Finset.sum_filter] at h1
  rw [finsum_eq_sum_of_fintype]
  exact h1

end S_Subgroup_exists_int_forall_finsum_ite_eq_one
end P2MW
export P2MW.S_Subgroup_exists_int_forall_finsum_ite_eq_one (solution)
