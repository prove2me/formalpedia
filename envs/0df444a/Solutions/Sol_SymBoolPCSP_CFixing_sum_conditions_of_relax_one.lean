-- Prove2me | solution 1 for SymBoolPCSP.CFixing.sum_conditions_of_relax_one
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T18:25:39.245218+00:00
-- url     : https://prove2.me/submissions/7916e890-3ece-4d3b-974b-36ab9e0b6494

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_FinsetParts_exists_parts_card_eq

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_sum_conditions_of_relax_one

theorem hw_eq_sum {k : ℕ} (x : Fin k → Bool) : hw x = ∑ i, if x i = true then 1 else 0 := by
  unfold hw; rw [Finset.card_filter]

theorem neg_indicator {L : ℕ} (X : Finset (Fin L)) : neg (indicator X) = indicator Xᶜ := by
  funext l; simp [neg, indicator]

theorem sum_mem_parts {L n : ℕ} {X : Finset (Fin L)} {Y : Fin n → Finset (Fin L)}
    (hYX : ∀ i, Y i ⊆ X) (hu : ∀ x ∈ X, ∃! i, x ∈ Y i) (l : Fin L) :
    (∑ i, if l ∈ Y i then 1 else 0 : ℕ) = if l ∈ X then 1 else 0 := by
  split_ifs with hl
  · obtain ⟨i, hi, hiu⟩ := hu l hl
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj; simp only [ite_eq_right_iff]; intro h; exact absurd (hiu j h) hj
    · simp
  · apply Finset.sum_eq_zero; intro i _; simp only [ite_eq_right_iff]; intro h
    exact absurd (hYX i h) hl

theorem core {L m r K : ℕ} {P Q : Set ℕ} (f : (Fin L → Bool) → Bool)
    (hf : PolOf (Ham K P) (Ham K Q) f) (hK : m + r = K) (X : Finset (Fin L))
    (Y : Fin m → Finset (Fin L)) (hYX : ∀ i, Y i ⊆ X) (hu : ∀ x ∈ X, ∃! i, x ∈ Y i)
    (Z : Fin r → Finset (Fin L))
    (hrow : ∀ l, (if l ∈ X then 1 else 0) + (∑ j, if l ∈ Z j then 1 else 0) ∈ P) :
    (∑ i, if f (indicator (Y i)) = true then 1 else 0) +
      (∑ j, if f (indicator (Z j)) = true then 1 else 0) ∈ Q := by
  subst hK
  have h := hf (fun l => Fin.append (fun i => decide (l ∈ Y i)) (fun j => decide (l ∈ Z j)))
    (fun l => by
      show hw _ ∈ P
      rw [hw_eq_sum, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, decide_eq_true_eq]
      rw [sum_mem_parts hYX hu]; exact hrow l)
  change hw _ ∈ Q at h
  rw [hw_eq_sum, Fin.sum_univ_add] at h
  simp only [Fin.append_left, Fin.append_right] at h; exact h

end Aux_sum_conditions_of_relax_one

open Aux_sum_conditions_of_relax_one in
/-- Sum conditions from the first relaxation of Lemma 4.5: let `k ≥ 2` and let `f` be a folded polymorphism of `(Ham_k({1}), Ham_k({0,…,k−2} ∪ {k}))`. Fix `T ⊆ [L]` and let `S_β` (`β ∈ {0,1}`) be the set of `s` such that `f(e_X) = β` for every `X ⊆ T` with `|X| = s`. Then any sum of `k − 1` elements of `S₁` lies in `S₀`, and `a + b₁ + ⋯ + b_{k−2} ∈ S₁` whenever `a ∈ S₀` and all `bᵢ ∈ S₁`. -/
theorem sum_conditions_of_relax_one {k L : ℕ} (hk : 2 ≤ k) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k})) f)
    (T : Finset (Fin L)) (S₀ S₁ : Set ℕ)
    (hS₀ : ∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false)
    (hS₁ : ∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) :
    (∀ b : Fin (k - 1) → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) ∧
    (∀ a ∈ S₀, ∀ b : Fin (k - 1 - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega] at hf
  generalize hA : m + 2 - 1 - 1 = A
  generalize hB : m + 2 - 1 = B
  obtain rfl : m = A := by omega
  obtain rfl : B = m + 1 := by omega
  refine ⟨fun b hb => ?_, fun a ha b hb => ?_⟩
  · rw [hS₀]; intro X hXT hXc
    obtain ⟨Y, hYX, hYc, hu⟩ := FinsetParts.exists_parts_card_eq X b hXc.symm
    have h := core f hf (m := m + 1) (r := 1) (by omega) X Y hYX hu (fun _ => Xᶜ)
      (fun l => by by_cases hl : l ∈ X <;> simp [hl])
    have hY1 : ∀ i, f (indicator (Y i)) = true := fun i =>
      (hS₁ (b i)).mp (hb i) (Y i) ((hYX i).trans hXT) (hYc i)
    simp only [hY1, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, Finset.univ_unique] at h
    rw [hfold, neg_indicator]
    cases hc : f (indicator Xᶜ) <;> simp [hc] at h ⊢ <;> omega
  · rw [hS₁]; intro X hXT hXc
    obtain ⟨Y0, hY0X, hY0c⟩ := Finset.exists_subset_card_eq (show a ≤ X.card by omega)
    obtain ⟨Y, hYX, hYc, hu⟩ := FinsetParts.exists_parts_card_eq (X \ Y0) b
      (by rw [Finset.card_sdiff_of_subset hY0X]; omega)
    have h := core f hf (m := m) (r := 2) (by omega) (X \ Y0) Y hYX hu ![Y0, Xᶜ]
      (fun l => by
        rcases em (l ∈ Y0) with h0 | h0
        · rw [Fin.sum_univ_two]; simp [h0, hY0X h0]
        · rw [Fin.sum_univ_two]; by_cases hl : l ∈ X <;> simp [hl, h0])
    have hY0 : f (indicator Y0) = false := (hS₀ a).mp ha Y0 (hY0X.trans hXT) hY0c
    have hY1 : ∀ i, f (indicator (Y i)) = true := fun i =>
      (hS₁ (b i)).mp (hb i) (Y i) ((hYX i).trans (Finset.sdiff_subset.trans hXT)) (hYc i)
    simp only [hY1, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at h
    rw [Fin.sum_univ_two] at h; simp [hY0] at h
    rw [hfold, neg_indicator]
    cases hc : f (indicator Xᶜ) <;> simp [hc] at h ⊢ <;> omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k L : ℕ} (hk : 2 ≤ k) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k})) f)
    (T : Finset (Fin L)) (S₀ S₁ : Set ℕ)
    (hS₀ : ∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false)
    (hS₁ : ∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) :
    (∀ b : Fin (k - 1) → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) ∧
    (∀ a ∈ S₀, ∀ b : Fin (k - 1 - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) :=
  SymBoolPCSP.CFixing.sum_conditions_of_relax_one hk f hfold hf T S₀ S₁ hS₀ hS₁
