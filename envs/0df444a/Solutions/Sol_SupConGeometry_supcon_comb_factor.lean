-- Prove2me | solution 1 for SupConGeometry.supcon_comb_factor
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:33:44.650916+00:00
-- url     : https://prove2.me/submissions/83669db4-8678-4bf8-9ac2-4d66b0e6c5f2

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

lemma cf_cls {N K b : ℕ} (Y : Fin N → Fin K) (y : Fin K) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ x, (Y (σ x) = y ↔ Y x = y)) (B : Sym (Fin N) b) :
    batchClass Y ((Sym.map σ B : Sym (Fin N) b) : Multiset (Fin N)) y
      = (batchClass Y (B : Multiset (Fin N)) y).map σ := by
  simp only [batchClass, Sym.coe_map, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro x _; simp [hσ]

lemma cf_clsc {N K b : ℕ} (Y : Fin N → Fin K) (y : Fin K) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ x, (Y (σ x) = y ↔ Y x = y)) (B : Sym (Fin N) b) :
    batchClassCompl Y ((Sym.map σ B : Sym (Fin N) b) : Multiset (Fin N)) y
      = (batchClassCompl Y (B : Multiset (Fin N)) y).map σ := by
  simp only [batchClassCompl, Sym.coe_map, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro x _; simp [hσ]

lemma cf_inv {N K b : ℕ} (Y : Fin N → Fin K) (y : Fin K) (l : ℕ) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ x, (Y (σ x) = y ↔ Y x = y)) (n m : Fin N) :
    ∑ B ∈ batchesWithCount Y b y l,
      ((Multiset.count (σ n) (batchClass Y (B : Multiset (Fin N)) y) : ℝ) *
        (Multiset.count (σ m) (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ)) =
    ∑ B ∈ batchesWithCount Y b y l,
      ((Multiset.count n (batchClass Y (B : Multiset (Fin N)) y) : ℝ) *
        (Multiset.count m (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ)) := by
  have hσ' : ∀ x, (Y (σ.symm x) = y ↔ Y x = y) := fun x => by
    conv_rhs => rw [← σ.apply_symm_apply x]
    rw [hσ]
  symm
  apply Finset.sum_nbij' (fun B => Sym.map σ B) (fun B => Sym.map σ.symm B)
  · intro B hB
    simp only [batchesWithCount, mem_filter, mem_univ, true_and] at hB ⊢
    rw [cf_cls Y y σ hσ, Multiset.card_map, hB]
  · intro B hB
    simp only [batchesWithCount, mem_filter, mem_univ, true_and] at hB ⊢
    rw [cf_cls Y y σ.symm hσ', Multiset.card_map, hB]
  · intro B _
    simp [Sym.map_map]
  · intro B _
    simp [Sym.map_map]
  · intro B _
    rw [cf_cls Y y σ hσ, cf_clsc Y y σ hσ, Multiset.count_map_eq_count' _ _ σ.injective,
      Multiset.count_map_eq_count' _ _ σ.injective]


lemma cf_sum {N K : ℕ} (Y : Fin N → Fin K) (y : Fin K) (M : Multiset (Fin N))
    (p : Fin N → Prop) [DecidablePred p] (hM : ∀ x ∈ M, p x) :
    ∑ x ∈ univ.filter p, (Multiset.count x M : ℝ) = (Multiset.card M : ℝ) := by
  rw [← Nat.cast_sum]; congr 1
  rw [Multiset.sum_count_eq_card]
  intro a ha; simp [hM a ha]

end SupConGeometry

open SupConGeometry in
theorem solution {N K b : ℕ} (hb : 3 ≤ b) (Y : Fin N → Fin K) (y : Fin K) (l : ℕ)
    (hl : 1 ≤ l) (hlb : l < b) (n m : Fin N) (hn : Y n = y) (hm : Y m ≠ y) :
    combFactor Y b y l n m =
      ((batchesWithCount Y b y l).card : ℝ) /
        ((labelCount Y y : ℝ) * ((N : ℝ) - (labelCount Y y : ℝ))) := by
  set S : Fin N → Fin N → ℝ := fun n m => ∑ B ∈ batchesWithCount Y b y l,
      ((Multiset.count n (batchClass Y (B : Multiset (Fin N)) y) : ℝ) *
        (Multiset.count m (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ)) with hS
  set P := univ.filter (fun x : Fin N => Y x = y) with hP
  set Q := univ.filter (fun x : Fin N => ¬ Y x = y) with hQ
  have hconst : ∀ n' ∈ P, ∀ m' ∈ Q, S n' m' = S n m := by
    intro n' hn' m' hm'
    simp only [hP, hQ, mem_filter, mem_univ, true_and] at hn' hm'
    have h2 : n' ≠ m' := by rintro rfl; exact hm' hn'
    have h3 : n ≠ m' := by rintro rfl; exact hm' hn
    let σ : Equiv.Perm (Fin N) := (Equiv.swap m m').trans (Equiv.swap n n')
    have hσ : ∀ x, (Y (σ x) = y ↔ Y x = y) := by
      intro x
      have e1 : ∀ z, (Y (Equiv.swap n n' z) = y ↔ Y z = y) := by
        intro z; rcases eq_or_ne z n with rfl | hz
        · simp [hn, hn']
        rcases eq_or_ne z n' with rfl | hz'
        · simp [hn, hn']
        · rw [Equiv.swap_apply_of_ne_of_ne hz hz']
      have e2 : ∀ z, (Y (Equiv.swap m m' z) = y ↔ Y z = y) := by
        intro z; rcases eq_or_ne z m with rfl | hz
        · simp [hm, hm']
        rcases eq_or_ne z m' with rfl | hz'
        · simp [hm, hm']
        · rw [Equiv.swap_apply_of_ne_of_ne hz hz']
      simp only [σ, Equiv.trans_apply, e1, e2]
    have hσn : σ n = n' := by
      simp only [σ, Equiv.trans_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hm hn) h3, Equiv.swap_apply_left]
    have hσm : σ m = m' := by
      simp only [σ, Equiv.trans_apply]
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm h3) (Ne.symm h2)]
    rw [← hσn, ← hσm]
    exact cf_inv Y y l σ hσ n m
  have hn0 : n ∈ P := by simp [hP, hn]
  have hm0 : m ∈ Q := by simp [hQ, hm]
  have htot : ∑ n' ∈ P, ∑ m' ∈ Q, S n' m' = ((batchesWithCount Y b y l).card : ℝ) * (l * (b - l)) := by
    have hB : ∀ B ∈ batchesWithCount Y b y l,
        (∑ n' ∈ P, (Multiset.count n' (batchClass Y (B : Multiset (Fin N)) y) : ℝ)) *
        (∑ m' ∈ Q, (Multiset.count m' (batchClassCompl Y (B : Multiset (Fin N)) y) : ℝ)) =
          (l : ℝ) * (b - l) := by
      intro B hBm
      simp only [batchesWithCount, mem_filter, mem_univ, true_and] at hBm
      rw [hP, hQ, cf_sum Y y (batchClass Y (B : Multiset (Fin N)) y) (fun x => Y x = y)
          (by intro x hx; simp only [batchClass, Multiset.mem_filter] at hx; exact hx.2),
        cf_sum Y y (batchClassCompl Y (B : Multiset (Fin N)) y) (fun x => ¬ Y x = y)
          (by intro x hx; simp only [batchClassCompl, Multiset.mem_filter] at hx; exact hx.2), hBm]
      have := Multiset.filter_add_not (fun j => Y j = y) (B : Multiset (Fin N))
      have hc := congrArg Multiset.card this
      rw [Multiset.card_add, Sym.card_coe] at hc
      have : Multiset.card (batchClassCompl Y (B : Multiset (Fin N)) y) = b - l := by
        rw [batchClassCompl]; simp only [ne_eq]; rw [batchClass] at hBm; omega
      rw [this, Nat.cast_sub hlb.le]
    simp only [hS]
    rw [sum_congr rfl (fun _ _ => Finset.sum_comm), Finset.sum_comm]
    rw [sum_congr rfl (fun B hBm => (Finset.sum_mul_sum _ _ _ _).symm.trans (hB B hBm))]
    simp [sum_const, nsmul_eq_mul]
  have htot2 : ∑ n' ∈ P, ∑ m' ∈ Q, S n' m' = (P.card : ℝ) * Q.card * S n m := by
    rw [Finset.sum_congr rfl (fun n' hn' => Finset.sum_congr rfl (fun m' hm' => hconst n' hn' m' hm'))]
    simp [sum_const, nsmul_eq_mul]; ring
  have hPc : (P.card : ℝ) = labelCount Y y := rfl
  have hQc : (Q.card : ℝ) = N - labelCount Y y := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N))) (fun x : Fin N => Y x = y)
    simp only [card_univ, Fintype.card_fin] at this
    have h' : ((labelCount Y y + Q.card : ℕ) : ℝ) = N := by exact_mod_cast this
    push_cast at h'; linarith
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast card_pos.mpr ⟨n, hn0⟩
  have hQpos : (0 : ℝ) < Q.card := by exact_mod_cast card_pos.mpr ⟨m, hm0⟩
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hbl : (0 : ℝ) < (b : ℝ) - l := by
    have : (l : ℝ) < b := by exact_mod_cast hlb
    linarith
  rw [combFactor, ← hQc, ← hPc]
  change 1 / ((l : ℝ) * ((b : ℝ) - l)) * S n m = _
  have := htot.symm.trans htot2
  field_simp
  nlinarith [this]
