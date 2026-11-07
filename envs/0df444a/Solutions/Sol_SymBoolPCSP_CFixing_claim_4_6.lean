-- Prove2me | solution 1 for SymBoolPCSP.CFixing.claim_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:12:17.722907+00:00
-- url     : https://prove2.me/submissions/0d94ad3c-46bf-4eea-a446-bf220da14f1f

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_mem_ATImage_ham_of_sign_sum
import Theorems.Thm_SymBoolPCSP_CFixing_image_subset_of_conservative

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_claim_4_6

theorem const_of_mem_ham0k {k : ℕ} {x : Fin k → Bool} (hx : x ∈ Ham k {0, k}) :
    (∀ c, x c = false) ∨ (∀ c, x c = true) := by
  simp only [Ham, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hw] at hx
  rcases hx with h | h
  · left; intro c
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    simpa using h (Finset.mem_univ c)
  · right; intro c
    have : Finset.univ.filter (fun i => x i = true) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h)
    have hc := Finset.mem_univ c
    rw [← this, Finset.mem_filter] at hc
    exact hc.2

theorem subset_image_of_proj {k L : ℕ} (f : (Fin L → Bool) → Bool) (j : Fin L)
    (hf : ∀ v, f v = v j) (P : Set (Fin k → Bool)) : P ⊆ image f P := by
  intro x hx
  exact ⟨fun _ => x, fun _ => hx, by funext c; simp [hf]⟩

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

theorem sum_boole_hw {k : ℕ} (x : Fin k → Bool) :
    ∑ c, (if x c then (1 : ℤ) else 0) = (hw x : ℤ) := by
  unfold hw; rw [Finset.sum_boole]

theorem hw_eq_zero_iff {k : ℕ} (y : Fin k → Bool) : hw y = 0 ↔ ∀ c, y c = false := by
  simp [hw, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem hw_eq_k_iff {k : ℕ} (y : Fin k → Bool) : hw y = k ↔ ∀ c, y c = true := by
  constructor
  · intro h c
    have : Finset.univ.filter (fun i => y i = true) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa [hw] using h)
    have hc := Finset.mem_univ c
    rw [← this, Finset.mem_filter] at hc
    exact hc.2
  · intro h; simp [hw, h]

theorem hw_le {k : ℕ} (y : Fin k → Bool) : hw y ≤ k := by
  unfold hw; exact (Finset.card_filter_le _ _).trans (by simp)

theorem ATImage_sum {k : ℕ} {P : Set (Fin k → Bool)} {y : Fin k → Bool} (hy : y ∈ ATImage P) :
    ∃ s : Fin k → ℤ, (∀ c, y c = decide (0 < s c)) ∧ ∃ L, Odd L ∧
      ∃ M : Fin L → Fin k → Bool, (∀ l, M l ∈ P) ∧
      ∑ c, s c = ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) * hw (M i) := by
  obtain ⟨L, hL, M, hM, rfl⟩ := hy
  refine ⟨fun c => ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) * (if M i c then 1 else 0),
    fun c => rfl, L, hL, M, hM, ?_⟩
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_sum, sum_boole_hw]

end Aux_claim_4_6

open Aux_claim_4_6 in
theorem claim_4_6 (k : ℕ) (hk : 1 ≤ k) :
    ATImage (Ham k {0}) = Ham k {0} ∧
    ATImage (Ham k {k}) = Ham k {k} ∧
    ATImage (Ham k {0, k}) = Ham k {0, k} ∧
    (2 ≤ k → ∀ l : ℕ, 1 ≤ l → l ≤ k - 1 → ATImage (Ham k {l}) = Ham k (Set.Icc 1 (k - 1))) ∧
    (2 ≤ k → ∀ l₁ l₂ : ℕ, l₁ ≤ k → l₂ ≤ k → ({l₁, l₂} : Set ℕ) ≠ {0, k} → l₁ ≠ l₂ →
      ATImage (Ham k {l₁, l₂}) = Set.univ) := by
  have hAT1 : ∀ P : Set (Fin k → Bool), P ⊆ ATImage P := fun P x hx =>
    ⟨1, odd_one, subset_image_of_proj (AT 1) 0
      (fun v => by cases h : v 0 <;> simp [AT, h] <;> exact ⟨0, by simp [h]⟩) P hx⟩
  have hATsub : ∀ P : Set (Fin k → Bool), P ⊆ Ham k {0, k} → ATImage P ⊆ P := by
    rintro P hP y ⟨L, hL, hy⟩
    exact image_subset_of_conservative (AT L) (AT_conservative hL) P hP hy
  have h0k : ∀ T : Set ℕ, T ⊆ {0, k} → Ham k T ⊆ Ham k {0, k} := fun T hT x hx => hT hx
  refine ⟨Set.Subset.antisymm (hATsub _ (h0k _ (by simp))) (hAT1 _),
    Set.Subset.antisymm (hATsub _ (h0k _ (by simp))) (hAT1 _),
    Set.Subset.antisymm (hATsub _ subset_rfl) (hAT1 _), ?_, ?_⟩
  · intro hk2 l hl1 hlk
    ext y; constructor
    · intro hy
      obtain ⟨s, hs, L, hL, M, hM, hsum⟩ := ATImage_sum hy
      have hrow : ∀ i, hw (M i) = l := fun i => hM i
      simp only [hrow] at hsum
      rw [← Finset.sum_mul, sum_neg_one_pow_odd hL, one_mul] at hsum
      show hw y ∈ Set.Icc 1 (k - 1)
      have hyk := hw_le y
      constructor
      · by_contra h0
        have hall := (hw_eq_zero_iff y).mp (by omega)
        have : ∑ c, s c ≤ 0 := Finset.sum_nonpos (fun c _ => by
          have := hs c; rw [hall c] at this; simpa using this.symm)
        omega
      · by_contra h0
        have hall := (hw_eq_k_iff y).mp (by omega)
        have : ∑ c : Fin k, (1 : ℤ) ≤ ∑ c, s c := Finset.sum_le_sum (fun c _ => by
          have := hs c; rw [hall c] at this
          have h' : 0 < s c := by simpa using this.symm
          omega)
        simp at this
        omega
    · intro hy
      have hy' : 1 ≤ hw y ∧ hw y ≤ k - 1 := hy
      refine mem_ATImage_ham_of_sign_sum (S := {l}) (l' := l) (Set.mem_singleton l) hl1 (by omega)
        (Set.mem_singleton l) (by omega) y l
        (by simp) ?_
      by_cases hle : hw y ≤ l
      · left
        refine ⟨?_, by exact_mod_cast hle⟩
        by_contra hn; push Not at hn
        have := (hw_eq_zero_iff y).mpr (fun c => by simpa using hn c); omega
      · right
        refine ⟨?_, by push Not at hle; exact_mod_cast hle.le⟩
        by_contra hn; push Not at hn
        have := (hw_eq_k_iff y).mpr (fun c => by simpa using hn c); omega
  · intro hk2 l₁ l₂ h1 h2 hne hneq
    obtain ⟨l, l', hl, hl', hl1, hlk, hl'k, hd⟩ : ∃ l l', l ∈ ({l₁, l₂} : Set ℕ) ∧
        l' ∈ ({l₁, l₂} : Set ℕ) ∧ 1 ≤ l ∧ l + 1 ≤ k ∧ l' ≤ k ∧ l ≠ l' := by
      by_cases hA : 1 ≤ l₁ ∧ l₁ + 1 ≤ k
      · exact ⟨l₁, l₂, by simp, by simp, hA.1, hA.2, h2, hneq⟩
      · refine ⟨l₂, l₁, by simp, by simp, ?_, ?_, h1, Ne.symm hneq⟩ <;>
        · by_contra hB
          apply hne
          have : (l₁ = 0 ∧ l₂ = k) ∨ (l₁ = k ∧ l₂ = 0) := by omega
          rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Set.pair_comm _ _
    ext y
    simp only [Set.mem_univ, iff_true]
    set d : ℤ := (l' : ℤ) - l with hdd
    have hd0 : d ≠ 0 := by rw [hdd]; omega
    have hdd1 : 1 ≤ d * d := by
      rcases lt_or_gt_of_ne hd0 with h | h <;> nlinarith
    have hyk := hw_le y
    by_cases hy : ∃ c, y c = true
    · refine mem_ATImage_ham_of_sign_sum hl hl1 hlk hl' hl'k y (l + d * (d * k))
        ⟨d * k, by ring⟩ (Or.inl ⟨hy, ?_⟩)
      have : (k : ℤ) ≤ d * (d * k) := by nlinarith
      omega
    · push Not at hy
      have h0 : hw y = 0 := (hw_eq_zero_iff y).mpr (fun c => by simpa using hy c)
      refine mem_ATImage_ham_of_sign_sum hl hl1 hlk hl' hl'k y (l - d * (d * k))
        ⟨-(d * k), by ring⟩ (Or.inr ⟨⟨⟨0, by omega⟩, by simpa using hy _⟩, ?_⟩)
      have : (k : ℤ) ≤ d * (d * k) := by nlinarith
      rw [h0]; push_cast; omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution (k : ℕ) (hk : 1 ≤ k) :
    ATImage (Ham k {0}) = Ham k {0} ∧
    ATImage (Ham k {k}) = Ham k {k} ∧
    ATImage (Ham k {0, k}) = Ham k {0, k} ∧
    (2 ≤ k → ∀ l : ℕ, 1 ≤ l → l ≤ k - 1 → ATImage (Ham k {l}) = Ham k (Set.Icc 1 (k - 1))) ∧
    (2 ≤ k → ∀ l₁ l₂ : ℕ, l₁ ≤ k → l₂ ≤ k → ({l₁, l₂} : Set ℕ) ≠ {0, k} → l₁ ≠ l₂ →
      ATImage (Ham k {l₁, l₂}) = Set.univ) :=
  SymBoolPCSP.CFixing.claim_4_6 k hk
