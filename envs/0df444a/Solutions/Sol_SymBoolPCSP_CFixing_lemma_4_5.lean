-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:43:31.3425+00:00
-- url     : https://prove2.me/submissions/1518f954-7bab-4f2e-98b6-73f5f54dab85

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_isSymmetricRel_eq_ham
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_5_single

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_lemma_4_5

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem exists_bad_rel {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) {L : ℕ}
    (g : (Fin L → Bool) → Bool) (hg : ¬ IsPolymorphism 𝔸 𝔹 g) :
    ∃ (R : τ) (S T : Set ℕ), S ⊆ T ∧ T ⊆ Set.Iic (ar R) ∧ 𝔸.rel R = Ham (ar R) S ∧
      𝔹.rel R = Ham (ar R) T ∧ ∃ y ∈ image g (Ham (ar R) S), hw y ∉ T := by
  unfold IsPolymorphism at hg
  push Not at hg
  obtain ⟨R, M, hM, hout⟩ := hg
  have hA := isSymmetricRel_eq_ham (hsym R).1
  have hB := isSymmetricRel_eq_ham (hsym R).2
  refine ⟨R, _, _, ?_, ?_, hA, hB, fun c => g (fun l => M l c), ?_, ?_⟩
  · rintro s ⟨x, hx, rfl⟩; exact ⟨x, hPF R hx, rfl⟩
  · rintro s ⟨x, _, rfl⟩; exact hw_le' x
  · rw [← hA]; exact ⟨M, hM, rfl⟩
  · intro h; apply hout; rw [hB]; exact h

end Aux_lemma_4_5

open Aux_lemma_4_5 in
theorem lemma_4_5 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ IsRelaxation 𝔸 𝔹 (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k}))) ∨
      (2 ≤ k ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {0, b}) (Ham k (Set.Iic (k - 1)))) := by
  obtain ⟨R, S, T, hST, hT, hA, hB, y, hy, hyT⟩ := exists_bad_rel 𝔸 𝔹 hPF hsym _ hAT
  have hpol : ∀ (L' : ℕ) (f : (Fin L' → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      PolOf (Ham (ar R) S) (Ham (ar R) T) f := fun L' f hp => by
    rw [← hA, ← hB]; exact hp R
  obtain ⟨k', ⟨hk, H⟩ | ⟨hk, b, hb1, hb2, H⟩⟩ := lemma_4_5_single hST hT ⟨L, hL, hy⟩ hyT
  · exact ⟨k', Or.inl ⟨hk, fun L' f hp =>
      H L' f (hidem L' f hp) (hfold L' f hp) (hpol L' f hp)⟩⟩
  · exact ⟨k', Or.inr ⟨hk, b, hb1, hb2, fun L' f hp =>
      H L' f (hidem L' f hp) (hfold L' f hp) (hpol L' f hp)⟩⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ IsRelaxation 𝔸 𝔹 (Ham k {1}) (Ham k (Set.Iic (k - 2) ∪ {k}))) ∨
      (2 ≤ k ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {0, b}) (Ham k (Set.Iic (k - 1)))) :=
  SymBoolPCSP.CFixing.lemma_4_5 𝔸 𝔹 hPF hsym hfold hidem L hL hAT
