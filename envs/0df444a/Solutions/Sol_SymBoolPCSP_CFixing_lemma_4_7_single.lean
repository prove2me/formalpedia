-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_4_7_single
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:41:43.838726+00:00
-- url     : https://prove2.me/submissions/20ae145b-0857-4cbc-b330-eba3ea74287c

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_polOf_ham_pin
import Theorems.Thm_SymBoolPCSP_CFixing_polOf_ham_flip
import Theorems.Thm_SymBoolPCSP_CFixing_majImage_ham_upper
import Theorems.Thm_SymBoolPCSP_CFixing_image_negRel_of_folded
import Theorems.Thm_SymBoolPCSP_CFixing_image_subset_of_conservative

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_lemma_4_7_single

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem polOf_mono {k L : ℕ} {P Q P' Q' : Set (Fin k → Bool)} {f : (Fin L → Bool) → Bool}
    (hf : PolOf P Q f) (hP : P' ⊆ P) (hQ : Q ⊆ Q') : PolOf P' Q' f :=
  fun M hM => hQ (hf M (fun l => hP (hM l)))

theorem ham_subset {k : ℕ} {X Y : Set ℕ} (h : ∀ l ≤ k, l ∈ X → l ∈ Y) : Ham k X ⊆ Ham k Y :=
  fun x hx => h _ (hw_le' x) hx

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

theorem red47_1 {k M b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hM : M ∈ S) (hMb : M < b) (hb2 : b + 1 ≤ 2 * M) (hbk : b ≤ k) (hbT : b ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        X L f → PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = (2 * (b - M) + 1) + (2 * M - b - 1) + i := ⟨k - b, by omega⟩
  refine ⟨2 * (b - M) + 1, Or.inl ⟨by omega, ⟨b - M, rfl⟩, fun L f hi hfo hx => ?_⟩⟩
  have h := polOf_mono (hX L f hi hfo hx) (P' := Ham _ {M})
    (Q' := Ham _ (Set.Iic ((2 * (b - M) + 1) + (2 * M - b - 1) + i) \ {b}))
    (ham_subset fun l _ h => by rw [Set.mem_singleton_iff.mp h]; exact hM)
    (ham_subset fun l hl h => Set.mem_diff_of_mem (Set.mem_Iic.mpr hl)
      (fun e => hbT (by rw [Set.mem_singleton_iff] at e; subst e; exact h)))
  have h2 := polOf_ham_pin (n := 2 * (b - M) + 1) (j := 2 * M - b - 1) (i := i)
    (fun l h => by
      simp only [Set.mem_singleton_iff, Set.mem_diff, Set.mem_Iic] at h ⊢; omega)
    Set.diff_subset f hi hfo h
  exact polOf_mono h2 (ham_subset fun l hl h => by simp at h ⊢ <;> omega)
    (ham_subset fun l hl h => by simp at h ⊢ <;> omega)

theorem red47_2 {k ℓ₁ ℓ₂ b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (h₁ : ℓ₁ ∈ S) (h₂ : ℓ₂ ∈ S) (h1 : 1 ≤ ℓ₁) (h1b : ℓ₁ < b) (hb2 : b < ℓ₂) (h2k : ℓ₂ ≤ k)
    (hbT : b ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        X L f → PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = (ℓ₂ - ℓ₁ + 1) + (ℓ₁ - 1) + i := ⟨k - ℓ₂, by omega⟩
  refine ⟨ℓ₂ - ℓ₁ + 1, Or.inr ⟨by omega, b - ℓ₁ + 1, by omega, by omega,
    fun L f hi hfo hx => ?_⟩⟩
  have h := polOf_mono (hX L f hi hfo hx) (P' := Ham _ {ℓ₁, ℓ₂})
    (Q' := Ham _ (Set.Iic ((ℓ₂ - ℓ₁ + 1) + (ℓ₁ - 1) + i) \ {b}))
    (ham_subset fun l _ h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> assumption)
    (ham_subset fun l hl h => Set.mem_diff_of_mem (Set.mem_Iic.mpr hl)
      (fun e => hbT (by rw [Set.mem_singleton_iff] at e; subst e; exact h)))
  have h2 := polOf_ham_pin (n := ℓ₂ - ℓ₁ + 1) (j := ℓ₁ - 1) (i := i)
    (fun l h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff, Set.mem_Iic] at h ⊢
      omega)
    Set.diff_subset f hi hfo h
  exact polOf_mono h2 (ham_subset fun l hl h => by simp at h ⊢ <;> omega)
    (ham_subset fun l hl h => by simp at h ⊢ <;> omega)

theorem red47 {k ℓ m M b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hST : S ⊆ T) (hT : T ⊆ Set.Iic k) (hbk : b ≤ k) (hbT : b ∉ T)
    (hℓ : ℓ ∈ S) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ + 1 ≤ k)
    (hM : M ∈ S) (hMmax : ∀ s ∈ S, s ≤ M) (hbM : b + 1 ≤ 2 * M)
    (hm : m ∈ S) (hmmin : ∀ s ∈ S, m ≤ s) (hbm : (k - b) + 1 ≤ 2 * (k - m)) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        X L f → PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by
  have hXf : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f :=
    fun L f hi hfo hx => polOf_ham_flip hST f hfo (hX L f hi hfo hx)
  have hmem : ∀ {s}, s ∈ S → k - s ∈ {l | l ≤ k ∧ k - l ∈ S} := fun {s} hs => by
    have : s ≤ k := hT (hST hs)
    exact ⟨Nat.sub_le _ _, by rw [Nat.sub_sub_self this]; exact hs⟩
  have hnT : k - b ∉ {l | l ≤ k ∧ k - l ∈ T} := fun h =>
    hbT (by have := h.2; rwa [Nat.sub_sub_self hbk] at this)
  have hMk : M ≤ k := hT (hST hM)
  have hbS : ∀ s ∈ S, s ≠ b := fun s hs e => hbT (e ▸ hST hs)
  have hmM := hmmin _ hM
  have hmℓ := hmmin _ hℓ
  have hℓM := hMmax _ hℓ
  have h1 := hbS _ hℓ; have h2 := hbS _ hM; have h3 := hbS _ hm
  rcases Nat.lt_or_ge M b with hb | hb
  · exact red47_1 X hX hM hb hbM hbk hbT
  rcases Nat.lt_or_ge b m with hb' | hb'
  · exact red47_1 X hXf (hmem hm) (by omega) (by omega) (Nat.sub_le _ _) hnT
  rcases Nat.lt_or_gt_of_ne h1 with h | h
  · exact red47_2 X hX hℓ hM hℓ1 h (by omega) hMk hbT
  · exact red47_2 X hXf (hmem hℓ) (hmem hm) (by omega) (by omega) (by omega) (Nat.sub_le _ _) hnT

end Aux_lemma_4_7_single

open Aux_lemma_4_7_single in
/-- Lemma 4.7 for a single symmetric promise relation: if `S ⊆ T ⊆ {0,…,k}` and some `y ∈ Maj(Ham_k(S))` has weight outside `T`, then every idempotent folded polymorphism of `(Ham_k(S), Ham_k(T))` is a polymorphism of `(Ham_{k'}({(k'+1)/2}), Ham_{k'}({0,…,k'-1}))` for some odd `k' ≥ 3`, or of `(Ham_{k'}({1,k'}), Ham_{k'}({0,…,k'} ∖ {b}))` for some `k' ≥ 3`, `2 ≤ b ≤ k'-1`. -/
theorem lemma_4_7_single {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ MajImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by
  have hyS : hw y ∉ S := fun h => hyT (hST h)
  have hSk : ∀ s ∈ S, s ≤ k := fun s hs => hT (hST hs)
  obtain ⟨ℓ, hℓS, hℓ1, hℓk⟩ : ∃ ℓ ∈ S, 1 ≤ ℓ ∧ ℓ + 1 ≤ k := by
    by_contra hne
    push Not at hne
    have hsub : Ham k S ⊆ Ham k {0, k} := fun x hx => by
      have h1 := hne _ hx; have h2 := hw_le' x
      show hw x ∈ ({0, k} : Set ℕ)
      by_cases h0 : hw x = 0
      · exact Or.inl h0
      · exact Or.inr (by have := h1 (by omega); show hw x = k; omega)
    obtain ⟨L, hL, hyL⟩ := hy
    exact hyS (image_subset_of_conservative (Maj L) (Maj_conservative hL) _ hsub hyL)
  have hfin : S.Finite := (Set.finite_Iic k).subset (hST.trans hT)
  obtain ⟨M, hMS, hMmax⟩ := Set.exists_max_image S id hfin ⟨ℓ, hℓS⟩
  obtain ⟨m, hmS, hmmin⟩ := Set.exists_min_image S id hfin ⟨ℓ, hℓS⟩
  have hMk := hSk M hMS
  have hmk := hSk m hmS
  have hmℓ := hmmin ℓ hℓS
  have hℓM := hMmax ℓ hℓS
  simp only [id] at hmℓ hℓM
  have hup := (majImage_ham_upper hℓS hℓ1 hMS hMk hMmax).1 y hy
  have hny : neg y ∈ MajImage (Ham k ((fun s => k - s) '' S)) := by
    rw [← negRel_ham S hSk, MajImage_negRel]; exact ⟨y, hy, rfl⟩
  have hlo := (majImage_ham_upper (S := (fun s => k - s) '' S) (l := k - ℓ) (w := k - m)
    ⟨ℓ, hℓS, rfl⟩ (by omega) ⟨m, hmS, rfl⟩ (Nat.sub_le _ _)
    (by rintro _ ⟨s, hs, rfl⟩; have := hmmin s hs; exact Nat.sub_le_sub_left this k)).1 _ hny
  rw [hw_neg] at hlo
  exact red47 (fun L f => PolOf (Ham k S) (Ham k T) f) (fun L f _ _ h => h) hST hT (hw_le' y) hyT
    hℓS hℓ1 hℓk hMS hMmax (by omega) hmS hmmin (by omega)

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ MajImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) :=
  SymBoolPCSP.CFixing.lemma_4_7_single hST hT hy hyT
