-- Prove2me | solution 1 for SymBoolPCSP.CFixing.claim_4_8
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:12:18.638872+00:00
-- url     : https://prove2.me/submissions/52277c2d-ff75-479b-8f38-9879f6fa6ebf

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_image_subset_of_conservative
import Theorems.Thm_SymBoolPCSP_CFixing_image_negRel_of_folded
import Theorems.Thm_SymBoolPCSP_CFixing_majImage_ham_upper

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_claim_4_8

theorem subset_image_of_proj {k L : ℕ} (f : (Fin L → Bool) → Bool) (j : Fin L)
    (hf : ∀ v, f v = v j) (P : Set (Fin k → Bool)) : P ⊆ image f P := by
  intro x hx
  exact ⟨fun _ => x, fun _ => hx, by funext c; simp [hf]⟩

theorem Maj_conservative {L : ℕ} (hL : Odd L) (v : Fin L → Bool) : ∃ l, Maj L v = v l := by
  by_cases h : ∃ l, v l = Maj L v
  · obtain ⟨l, hl⟩ := h; exact ⟨l, hl.symm⟩
  · push Not at h
    exfalso
    have hL1 : 1 ≤ L := by obtain ⟨t, rfl⟩ := hL; omega
    cases hA : Maj L v
    · have : ∀ i, v i = true := fun i => by have := h i; rw [hA] at this; simpa using this
      have hwL : hw v = L := by simp [hw, this]
      simp only [Maj, hwL, decide_eq_false_iff_not] at hA
      omega
    · have : ∀ i, v i = false := fun i => by have := h i; rw [hA] at this; simpa using this
      simp [Maj, hw, this] at hA

theorem hw_neg {k : ℕ} (x : Fin k → Bool) : hw (neg x) = k - hw x := by
  have : hw x + hw (neg x) = k := by
    unfold hw neg
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i _ => show (if x i = true then 1 else 0) +
      (if (!x i) = true then 1 else 0) = 1 by cases x i <;> simp)]
    simp
  omega

theorem neg_neg' {k : ℕ} (x : Fin k → Bool) : neg (neg x) = x := by
  funext i; simp [neg]

theorem Maj_folded {L : ℕ} (hL : Odd L) : IsFolded (Maj L) := by
  intro x
  have h1 := hw_neg x
  have h2 : hw x ≤ L := by
    unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨t, rfl⟩ := hL
  simp only [Maj, h1]
  by_cases h : 2 * t + 1 < 2 * hw x
  · have : ¬ (2 * t + 1 < 2 * (2 * t + 1 - hw x)) := by omega
    simp [h, this]
  · have : 2 * t + 1 < 2 * (2 * t + 1 - hw x) := by omega
    simp [h, this]

theorem MajImage_negRel {k : ℕ} (P : Set (Fin k → Bool)) :
    MajImage (negRel P) = negRel (MajImage P) := by
  ext y; constructor
  · rintro ⟨L, hL, hy⟩
    rw [image_negRel_of_folded _ (Maj_folded hL)] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', ⟨L, hL, hy'⟩, rfl⟩
  · rintro ⟨y', ⟨L, hL, hy'⟩, rfl⟩
    refine ⟨L, hL, ?_⟩
    rw [image_negRel_of_folded _ (Maj_folded hL)]
    exact ⟨y', hy', rfl⟩

theorem negRel_ham {k : ℕ} (S : Set ℕ) (hS : ∀ s ∈ S, s ≤ k) :
    negRel (Ham k S) = Ham k ((fun s => k - s) '' S) := by
  ext x; constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨hw x', hx', (hw_neg x').symm⟩
  · rintro ⟨s, hs, hsx⟩
    refine ⟨neg x, ?_, neg_neg' x⟩
    show hw (neg x) ∈ S
    rw [hw_neg]; have := hS s hs; simp only at hsx; rw [← hsx]
    rwa [Nat.sub_sub_self this]

theorem hw_le {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

end Aux_claim_4_8

open Aux_claim_4_8 in
theorem claim_4_8 (k : ℕ) (hk : 1 ≤ k) :
    (∀ P : Set (Fin k → Bool), P ⊆ Ham k {0, k} → MajImage P = P) ∧
    (∀ (S : Finset ℕ) (hne : S.Nonempty), (∀ s ∈ S, s ≤ k) → (S \ {0, k}).Nonempty →
      MajImage (Ham k (S : Set ℕ)) =
        Ham k {b : ℕ | b ≤ k ∧ 2 * (S.min' hne : ℤ) - k + 1 ≤ b ∧
          (b : ℤ) ≤ 2 * (S.max' hne : ℤ) - 1}) := by
  refine ⟨fun P hP => Set.Subset.antisymm ?_ ?_, ?_⟩
  · rintro y ⟨L, hL, hy⟩
    exact image_subset_of_conservative (Maj L) (Maj_conservative hL) P hP hy
  · intro x hx
    refine ⟨1, odd_one, subset_image_of_proj (Maj 1) 0 (fun v => ?_) P hx⟩
    have : hw v = if v 0 = true then 1 else 0 := by
      unfold hw; rw [Finset.card_filter, Fin.sum_univ_one]
    cases h : v 0 <;> simp [Maj, this, h]
  · intro S hne hSk hcore
    obtain ⟨e, he⟩ := hcore
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at he
    obtain ⟨heS, he0, hek⟩ := he
    have hek' := hSk e heS
    set m0 := S.min' hne with hm0
    set M0 := S.max' hne with hM0
    have hm0S : m0 ∈ S := S.min'_mem hne
    have hM0S : M0 ∈ S := S.max'_mem hne
    have hm0e : m0 ≤ e := S.min'_le e heS
    have heM0 : e ≤ M0 := S.le_max' e heS
    have hSmax : ∀ s ∈ (S : Set ℕ), s ≤ M0 := fun s hs => S.le_max' s hs
    have hSk' : ∀ s ∈ (S : Set ℕ), s ≤ k := fun s hs => hSk s hs
    set S' : Set ℕ := (fun s => k - s) '' (S : Set ℕ) with hS'
    have hneg : negRel (Ham k (S : Set ℕ)) = Ham k S' := negRel_ham _ hSk'
    have hS'max : ∀ s ∈ S', s ≤ k - m0 := by
      rintro s ⟨t, ht, rfl⟩
      show k - t ≤ k - m0
      have : m0 ≤ t := S.min'_le t ht
      omega
    have hkm0 : k - m0 ∈ S' := ⟨m0, hm0S, rfl⟩
    have hke : k - e ∈ S' := ⟨e, heS, rfl⟩
    have hMajNeg : MajImage (Ham k S') = negRel (MajImage (Ham k (S : Set ℕ))) := by
      rw [← hneg, MajImage_negRel]
    ext y
    constructor
    · intro hy
      have hu := (majImage_ham_upper heS (by omega) hM0S (hSk _ hM0S) hSmax).1 y hy
      have hny : neg y ∈ MajImage (Ham k S') := by rw [hMajNeg]; exact ⟨y, hy, rfl⟩
      have hl := (majImage_ham_upper hke (by omega) hkm0 (by omega) hS'max).1 _ hny
      rw [hw_neg] at hl
      have := hw_le y
      show hw y ≤ k ∧ _ ∧ _
      refine ⟨this, ?_, ?_⟩ <;> omega
    · rintro ⟨hyk, hlo, hhi⟩
      by_cases hb : e ≤ hw y
      · exact (majImage_ham_upper heS (by omega) hM0S (hSk _ hM0S) hSmax).2 (hw y) hb hyk
          (by omega) (Set.mem_singleton (hw y))
      · have hn : neg y ∈ MajImage (Ham k S') :=
          (majImage_ham_upper hke (by omega) hkm0 (by omega) hS'max).2 (hw (neg y))
            (by rw [hw_neg]; omega) (hw_le _) (by rw [hw_neg]; omega) (Set.mem_singleton _)
        rw [hMajNeg] at hn
        obtain ⟨y', hy', hyy⟩ := hn
        have : y' = y := by rw [← neg_neg' y', hyy, neg_neg']
        rw [← this]; exact hy'

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution (k : ℕ) (hk : 1 ≤ k) :
    (∀ P : Set (Fin k → Bool), P ⊆ Ham k {0, k} → MajImage P = P) ∧
    (∀ (S : Finset ℕ) (hne : S.Nonempty), (∀ s ∈ S, s ≤ k) → (S \ {0, k}).Nonempty →
      MajImage (Ham k (S : Set ℕ)) =
        Ham k {b : ℕ | b ≤ k ∧ 2 * (S.min' hne : ℤ) - k + 1 ≤ b ∧
          (b : ℤ) ≤ 2 * (S.max' hne : ℤ) - 1}) :=
  SymBoolPCSP.CFixing.claim_4_8 k hk
