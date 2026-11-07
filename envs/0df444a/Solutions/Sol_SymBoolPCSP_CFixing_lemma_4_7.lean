-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:43:32.380025+00:00
-- url     : https://prove2.me/submissions/3d68e5ca-b6a7-47b7-b1a1-f846763651ad

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_isSymmetricRel_eq_ham
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_7_single

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_lemma_4_7

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

end Aux_lemma_4_7

open Aux_lemma_4_7 in
theorem lemma_4_7 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ Odd k ∧ IsRelaxation 𝔸 𝔹 (Ham k {(k + 1) / 2}) (Ham k (Set.Iic (k - 1)))) ∨
      (3 ≤ k ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {1, k}) (Ham k (Set.Iic k \ {b}))) := by
  obtain ⟨R, S, T, hST, hT, hA, hB, y, hy, hyT⟩ := exists_bad_rel 𝔸 𝔹 hPF hsym _ hMaj
  have hpol : ∀ (L' : ℕ) (f : (Fin L' → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      PolOf (Ham (ar R) S) (Ham (ar R) T) f := fun L' f hp => by
    rw [← hA, ← hB]; exact hp R
  obtain ⟨k', ⟨hk, hodd, H⟩ | ⟨hk, b, hb1, hb2, H⟩⟩ := lemma_4_7_single hST hT ⟨L, hL, hy⟩ hyT
  · exact ⟨k', Or.inl ⟨hk, hodd, fun L' f hp =>
      H L' f (hidem L' f hp) (hfold L' f hp) (hpol L' f hp)⟩⟩
  · exact ⟨k', Or.inr ⟨hk, b, hb1, hb2, fun L' f hp =>
      H L' f (hidem L' f hp) (hfold L' f hp) (hpol L' f hp)⟩⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L : ℕ) (hL : Odd L) (hMaj : ¬ IsPolymorphism 𝔸 𝔹 (Maj L)) :
    ∃ k : ℕ,
      (3 ≤ k ∧ Odd k ∧ IsRelaxation 𝔸 𝔹 (Ham k {(k + 1) / 2}) (Ham k (Set.Iic (k - 1)))) ∨
      (3 ≤ k ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k - 1 ∧
        IsRelaxation 𝔸 𝔹 (Ham k {1, k}) (Ham k (Set.Iic k \ {b}))) :=
  SymBoolPCSP.CFixing.lemma_4_7 𝔸 𝔹 hPF hsym hfold hidem L hL hMaj
