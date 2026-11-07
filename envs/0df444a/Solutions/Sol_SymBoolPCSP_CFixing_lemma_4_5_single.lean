-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_4_5_single
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:41:42.673196+00:00
-- url     : https://prove2.me/submissions/9cac7b4c-be08-46ec-904a-898f0bc3f956

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_polOf_ham_pin
import Theorems.Thm_SymBoolPCSP_CFixing_polOf_ham_flip
import Theorems.Thm_SymBoolPCSP_CFixing_claim_4_6
import Theorems.Thm_SymBoolPCSP_CFixing_image_subset_of_conservative

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_lemma_4_5_single

theorem hw_le' {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem polOf_mono {k L : ℕ} {P Q P' Q' : Set (Fin k → Bool)} {f : (Fin L → Bool) → Bool}
    (hf : PolOf P Q f) (hP : P' ⊆ P) (hQ : Q ⊆ Q') : PolOf P' Q' f :=
  fun M hM => hQ (hf M (fun l => hP (hM l)))

theorem ham_subset {k : ℕ} {X Y : Set ℕ} (h : ∀ l ≤ k, l ∈ X → l ∈ Y) : Ham k X ⊆ Ham k Y :=
  fun x hx => h _ (hw_le' x) hx

theorem sum_neg_one_pow_odd {L : ℕ} (hL : Odd L) : ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) = 1 := by
  obtain ⟨n, rfl⟩ := hL
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, pow_succ, pow_succ, show 2 * n + 1 = 2 * n + 1 from rfl,
      Odd.neg_one_pow (⟨n, rfl⟩ : Odd (2 * n + 1))]
    ring_nf; rw [Even.neg_one_pow ⟨n, by ring⟩]; norm_num

theorem AT_conservative {L : ℕ} (hL : Odd L) (v : Fin L → Bool) : ∃ l, AT L v = v l := by
  by_cases h : ∃ l, v l = AT L v
  · obtain ⟨l, hl⟩ := h; exact ⟨l, hl.symm⟩
  · push Not at h
    exfalso
    cases hA : AT L v
    · have : ∀ i, v i = true := fun i => by have := h i; rw [hA] at this; simpa using this
      simp only [AT, this, if_true, mul_one, sum_neg_one_pow_odd hL, decide_eq_false_iff_not] at hA
      exact hA one_pos
    · have : ∀ i, v i = false := fun i => by have := h i; rw [hA] at this; simpa using this
      simp [AT, this] at hA

theorem red45_A {k ℓ b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hℓ : ℓ ∈ S) (hℓ1 : 1 ≤ ℓ) (hℓb : ℓ < b) (hbk : b + 1 ≤ k) (hbT : b ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = (b - ℓ + 2) + (ℓ - 1) + i := ⟨k - b - 1, by omega⟩
  refine ⟨b - ℓ + 2, Or.inl ⟨by omega, fun L f hi hfo hx => ?_⟩⟩
  have h := polOf_mono (hX L f hi hfo hx) (P' := Ham _ {ℓ})
    (Q' := Ham _ (Set.Iic ((b - ℓ + 2) + (ℓ - 1) + i) \ {b}))
    (ham_subset fun l _ h => by rw [Set.mem_singleton_iff.mp h]; exact hℓ)
    (ham_subset fun l hl h => Set.mem_diff_of_mem (Set.mem_Iic.mpr hl)
      (fun e => hbT (by rw [Set.mem_singleton_iff] at e; subst e; exact h)))
  have h2 := polOf_ham_pin (n := b - ℓ + 2) (j := ℓ - 1) (i := i)
    (fun l h => by
      simp only [Set.mem_singleton_iff, Set.mem_diff, Set.mem_Iic] at h ⊢; omega)
    Set.diff_subset f hi hfo h
  exact polOf_mono h2 (ham_subset fun l hl h => by simp at h ⊢ <;> omega)
    (ham_subset fun l hl h => by simp at h ⊢ <;> omega)

theorem red45_B {k ℓ ℓ' : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    (hℓ : ℓ ∈ S) (hℓ' : ℓ' ∈ S) (hlt : ℓ < ℓ') (hkT : k ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by
  have hℓ'k : ℓ' + 1 ≤ k := by
    have h1 : ℓ' ≤ k := hT (hST hℓ')
    have h2 : ℓ' ≠ k := fun e => hkT (e ▸ hST hℓ')
    omega
  obtain ⟨n, rfl⟩ : ∃ n, k = n + ℓ + 0 := ⟨k - ℓ, by omega⟩
  refine ⟨n, Or.inr ⟨by omega, ℓ' - ℓ, by omega, by omega, fun L f hi hfo hx => ?_⟩⟩
  have h := polOf_mono (hX L f hi hfo hx) (P' := Ham _ {ℓ, ℓ'})
    (Q' := Ham _ (Set.Iic (n + ℓ + 0) \ {n + ℓ + 0}))
    (ham_subset fun l _ h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> assumption)
    (ham_subset fun l hl h => Set.mem_diff_of_mem (Set.mem_Iic.mpr hl)
      (fun e => hkT (by rw [Set.mem_singleton_iff] at e; subst e; exact h)))
  have h2 := polOf_ham_pin (n := n) (j := ℓ) (i := 0)
    (fun l h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff, Set.mem_Iic] at h ⊢
      omega)
    Set.diff_subset f hi hfo h
  exact polOf_mono h2 (ham_subset fun l hl h => by simp at h ⊢ <;> omega)
    (ham_subset fun l hl h => by simp at h ⊢ <;> omega)

theorem red45 {k ℓ b : ℕ} {S T : Set ℕ} (X : ∀ L : ℕ, ((Fin L → Bool) → Bool) → Prop)
    (hX : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k S) (Ham k T) f)
    (hST : S ⊆ T) (hT : T ⊆ Set.Iic k) (hbk : b ≤ k) (hbT : b ∉ T)
    (hℓ : ℓ ∈ S) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ + 1 ≤ k)
    (h2 : b = 0 ∨ b = k → ∃ ℓ' ∈ S, ℓ' ≠ ℓ) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → X L f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by
  have hXf : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f → X L f →
      PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f :=
    fun L f hi hfo hx => polOf_ham_flip hST f hfo (hX L f hi hfo hx)
  have hSTf : {l | l ≤ k ∧ k - l ∈ S} ⊆ {l | l ≤ k ∧ k - l ∈ T} := fun l h => ⟨h.1, hST h.2⟩
  have hTf : {l | l ≤ k ∧ k - l ∈ T} ⊆ Set.Iic k := fun l h => h.1
  have hmem : ∀ {s}, s ∈ S → k - s ∈ {l | l ≤ k ∧ k - l ∈ S} := fun {s} hs => by
    have : s ≤ k := hT (hST hs)
    exact ⟨Nat.sub_le _ _, by rw [Nat.sub_sub_self this]; exact hs⟩
  have hnT : ∀ {s}, s ≤ k → s ∉ T → k - s ∉ {l | l ≤ k ∧ k - l ∈ T} := fun {s} hs hsT h =>
    hsT (by have := h.2; rwa [Nat.sub_sub_self hs] at this)
  have hℓb : ℓ ≠ b := fun e => hbT (e ▸ hST hℓ)
  rcases Nat.eq_zero_or_pos b with hb0 | hb0
  · obtain ⟨ℓ', hℓ'S, hne⟩ := h2 (Or.inl hb0)
    have hℓ'k : ℓ' ≤ k := hT (hST hℓ'S)
    have hkT : k ∉ {l | l ≤ k ∧ k - l ∈ T} := by
      have := hnT (s := b) hbk hbT; rwa [hb0, Nat.sub_zero] at this
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact red45_B X hXf hSTf hTf (hmem hℓ) (hmem hℓ'S) (by omega) hkT
    · exact red45_B X hXf hSTf hTf (hmem hℓ'S) (hmem hℓ) (by omega) hkT
  rcases eq_or_ne b k with hbk' | hbk'
  · obtain ⟨ℓ', hℓ'S, hne⟩ := h2 (Or.inr hbk')
    have hkT : k ∉ T := hbk' ▸ hbT
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact red45_B X hX hST hT hℓ'S hℓ h hkT
    · exact red45_B X hX hST hT hℓ hℓ'S h hkT
  rcases Nat.lt_or_gt_of_ne hℓb with h | h
  · exact red45_A X hX hℓ hℓ1 h (by omega) hbT
  · exact red45_A X hXf (hmem hℓ) (by omega) (by omega) (by omega) (hnT hbk hbT)

end Aux_lemma_4_5_single

open Aux_lemma_4_5_single in
/-- Lemma 4.5 for a single symmetric promise relation: if `S ⊆ T ⊆ {0,…,k}` and some `y ∈ AT(Ham_k(S))` has weight outside `T`, then every idempotent folded polymorphism of `(Ham_k(S), Ham_k(T))` is a polymorphism of `(Ham_{k'}({1}), Ham_{k'}({0,…,k'-2,k'}))` for some `k' ≥ 3`, or of `(Ham_{k'}({0,b}), Ham_{k'}({0,…,k'-1}))` for some `k' ≥ 2`, `1 ≤ b ≤ k'-1`. -/
theorem lemma_4_5_single {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ ATImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f → PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by
  have hyS : hw y ∉ S := fun h => hyT (hST h)
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
    exact hyS (image_subset_of_conservative (AT L) (AT_conservative hL) _ hsub hyL)
  refine red45 (fun L f => PolOf (Ham k S) (Ham k T) f) (fun L f _ _ h => h) hST hT (hw_le' y)
    hyT hℓS hℓ1 hℓk ?_
  intro hb
  by_contra hne
  push Not at hne
  have hS : Ham k S = Ham k {ℓ} := by
    ext x; exact ⟨fun h => hne _ h, fun h => show hw x ∈ S from (Set.mem_singleton_iff.mp h) ▸ hℓS⟩
  rw [hS, (claim_4_6 k (by omega)).2.2.2.1 (by omega) ℓ hℓ1 (by omega)] at hy
  have : hw y ∈ Set.Icc 1 (k - 1) := hy
  simp only [Set.mem_Icc] at this; omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ ATImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f → PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) :=
  SymBoolPCSP.CFixing.lemma_4_5_single hST hT hy hyT
