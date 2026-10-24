-- Prove2me | solution 1 for PersonalizedAssortment.IB.lemma2_never_offers_stocked_out
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:44:39.127358+00:00
-- url     : https://prove2.me/submissions/df9f0279-84e4-4649-9f50-928984119a91

import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators
open PersonalizedAssortment.IB

theorem solution {n : ℕ} {Z : Type*} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (c : Fin n → ℕ) (hc : ∀ i, 0 < c i) (𝒮 : Finset (Finset (Fin n)))
    (h𝒮 : ∅ ∈ 𝒮) (hdel : ∀ S ∈ 𝒮, ∀ j ∈ S, S.erase j ∈ 𝒮) (φ : Z → ChoiceModel n)
    (hsub : Substitutable 𝒮 φ) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (hsel : IsIBRule Ψ r c 𝒮 φ z sel)
    (t : Fin T) (I : Fin n → ℕ) (hI : ∀ i, I i ≤ c i) :
    ∀ i ∈ sel t I, 0 < I i := by
  classical
  intro i hi
  by_contra hpos
  have hi0 : I i = 0 := Nat.eq_zero_of_not_pos hpos
  let S := sel t I
  have hSi : i ∈ S := hi
  obtain ⟨hS, hmax, hmin⟩ := hsel t I
  have hdelete : S.erase i ∈ 𝒮 := hdel S hS i hSi
  have hweight (j : Fin n) : 0 ≤ Ψ ((I j : ℝ) / (c j : ℝ)) * r j := by
    have hcpos : (0 : ℝ) < c j := by exact_mod_cast hc j
    have hIreal : (I j : ℝ) ≤ c j := by exact_mod_cast hI j
    have hx : (I j : ℝ) / (c j : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hcpos.le, (div_le_one hcpos).mpr hIreal⟩
    exact mul_nonneg (hΨ.1 hx).1 (hr j).le
  have hcmp : ibIndex Ψ r c (φ (z t)) I S ≤ ibIndex Ψ r c (φ (z t)) I (S.erase i) := by
    unfold ibIndex
    calc
      _ = ∑ j ∈ S.erase i, Ψ ((I j : ℝ) / (c j : ℝ)) * r j * (φ (z t)).prob S j := by
        rw [← Finset.sum_erase_add _ _ hSi]
        simp [hi0, hΨ.2.2.1]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hp := hsub (z t) (S.erase i) hdelete j i hji
        rw [Finset.insert_erase hSi] at hp
        exact mul_le_mul_of_nonneg_left hp (hweight j)
  have heq : ibIndex Ψ r c (φ (z t)) I (S.erase i) = ibIndex Ψ r c (φ (z t)) I S :=
    le_antisymm (hmax (S.erase i) hdelete) hcmp
  have hcard : S.card ≤ (S.erase i).card := hmin (S.erase i) hdelete heq
  exact (Nat.not_lt_of_ge hcard) (Finset.card_erase_lt_of_mem hSi)

#print axioms solution
