-- Prove2me | solution 1 for VapnikChervonenkis.GrowthFunction.lemma1_shattered_subsample
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:53:02.121169+00:00
-- url     : https://prove2.me/submissions/fcf76450-3c8d-4024-9c96-e95460805c17

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction



namespace VapnikChervonenkis.GrowthFunction

open Finset Classical

noncomputable def vcTraces {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Finset (Finset (Fin r)) :=
  univ.filter (fun t : Finset (Fin r) => ∃ A ∈ S, ∀ i, i ∈ t ↔ x i ∈ A)

lemma vc_index_eq {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x = (vcTraces S x).card := by
  unfold Shared.index vcTraces; congr

lemma vc_index_le {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x ≤ 2 ^ r := by
  rw [vc_index_eq]
  calc (vcTraces S x).card ≤ (univ : Finset (Finset (Fin r))).card := card_le_univ _
    _ = 2 ^ r := by rw [card_univ, Fintype.card_finset, Fintype.card_fin]

lemma vc_Phi_eq_sum (n r : ℕ) : Shared.Phi n r = ∑ k ∈ range (n + 1), r.choose k := by
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => simp [Shared.Phi]
    | succ n => rw [Finset.sum_range_succ']; simp [Shared.Phi]
  | succ r ih =>
    cases n with
    | zero => simp [Shared.Phi]
    | succ n =>
      simp only [Shared.Phi]
      rw [ih, ih, Finset.sum_range_succ' (fun k => (r+1).choose k)]
      simp only [Nat.choose_succ_succ', Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun k => r.choose k) (n+1)]
      simp; ring

lemma vc_Phi_le (n : ℕ) (hn : 1 ≤ n) (r : ℕ) : Shared.Phi n r ≤ r ^ n + 1 := by
  induction n, hn using Nat.le_induction generalizing r with
  | base =>
    rw [vc_Phi_eq_sum]; simp [Finset.sum_range_succ]; omega
  | succ n hn ih =>
    induction r with
    | zero => simp [Shared.Phi]
    | succ r ihr =>
      simp only [Shared.Phi]
      have h1 := ih r
      have h2 : r ^ n < (r + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
      have h3 : (r + 1) ^ (n + 1) = (r+1)^n * r + (r+1)^n := by ring
      have h4 : r ^ n * r ≤ (r+1)^n * r := Nat.mul_le_mul_right _ h2.le
      have h5 : r ^ (n+1) = r ^ n * r := by ring
      omega

lemma vc_two_pow_le (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ n) : 2 ^ r ≤ r ^ n + 1 := by
  rcases Nat.lt_or_ge r 2 with h | h
  · interval_cases r
    · simp
    · simp
  · have := Nat.pow_le_pow_left h r
    have := Nat.pow_le_pow_right (by omega : 0 < r) hr
    omega

/-- If `vcTraces S x` shatters `T` with `#T = n`, the corresponding subsample has index `2^n`. -/
lemma vc_shatters_index {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X)
    (T : Finset (Fin r)) {n : ℕ} (h : T.card = n) (hT : (vcTraces S x).Shatters T) :
    Shared.index S (x ∘ (T.orderEmbOfFin h)) = 2 ^ n := by
  set e := T.orderEmbOfFin h with he
  rw [vc_index_eq]
  have : vcTraces S (x ∘ e) = univ := by
    apply Finset.eq_univ_of_forall
    intro t
    have hsub : t.map e.toEmbedding ⊆ T := by
      intro a ha
      simp only [mem_map] at ha
      obtain ⟨j, -, rfl⟩ := ha
      exact T.orderEmbOfFin_mem h j
    obtain ⟨u, hu, hTu⟩ := hT hsub
    simp only [vcTraces, mem_filter, mem_univ, true_and] at hu ⊢
    obtain ⟨A, hA, hAu⟩ := hu
    refine ⟨A, hA, fun j => ?_⟩
    have hj : e j ∈ T := T.orderEmbOfFin_mem h j
    have : j ∈ t ↔ e j ∈ T ∩ u := by
      rw [hTu]; simp
    rw [this, mem_inter, Function.comp_apply, ← hAu]; simp [hj]
  rw [this, card_univ, Fintype.card_finset, Fintype.card_fin]

/-- Sauer–Shelah: if no strictly increasing subsample of size `n` is shattered, then
the index is at most `∑_{k<n} C(r,k)`. -/
lemma vc_sauer {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) (n : ℕ)
    (h : ∀ e : Fin n → Fin r, StrictMono e → Shared.index S (x ∘ e) ≠ 2 ^ n) :
    Shared.index S x ≤ ∑ k ∈ range n, r.choose k := by
  rw [vc_index_eq]
  have hsh : ∀ T ∈ (vcTraces S x).shatterer, T.card < n := by
    intro T hT
    rw [mem_shatterer] at hT
    by_contra hc
    push_neg at hc
    obtain ⟨T', hT'T, hT'c⟩ := Finset.exists_subset_card_eq hc
    exact h _ (T'.orderEmbOfFin hT'c).strictMono
      (vc_shatters_index S x T' hT'c (hT.mono_right hT'T))
  refine (card_le_card_shatterer _).trans ?_
  have : (vcTraces S x).shatterer ⊆
      (range n).biUnion (fun k => powersetCard k (univ : Finset (Fin r))) := by
    intro T hT
    exact mem_biUnion.2 ⟨T.card, mem_range.2 (hsh T hT), mem_powersetCard_univ.2 rfl⟩
  refine (card_le_card this).trans (card_biUnion_le.trans ?_)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro k _
  rw [card_powersetCard, card_univ, Fintype.card_fin]

lemma vc_lemma1 {X : Type*} (S : Set (Set X)) (i n : ℕ) (x : Fin i → X)
    (hn1 : 1 ≤ n) (hni : n ≤ i) (hΔ : Shared.Phi n i ≤ Shared.index S x) :
    ∃ e : Fin n → Fin i, StrictMono e ∧ Shared.index S (x ∘ e) = 2 ^ n := by
  by_contra hc
  push_neg at hc
  have h1 := vc_sauer S x n (fun e he => hc e he)
  rw [vc_Phi_eq_sum, Finset.sum_range_succ] at hΔ
  have : 0 < i.choose n := Nat.choose_pos hni
  omega

lemma vc_index_le_growth {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x ≤ Shared.growthFunction S r := by
  unfold Shared.growthFunction
  exact le_ciSup (f := fun y : Fin r → X => Shared.index S y)
    ⟨2 ^ r, by rintro _ ⟨y, rfl⟩; exact vc_index_le S y⟩ x

lemma vc_growth_le {X : Type*} (S : Set (Set X)) (r B : ℕ)
    (h : ∀ x : Fin r → X, Shared.index S x ≤ B) : Shared.growthFunction S r ≤ B := by
  unfold Shared.growthFunction
  exact ciSup_le' h

lemma vc_index_lt_phi {X : Type*} (S : Set (Set X)) (n : ℕ)
    (hn : Shared.growthFunction S n ≠ 2 ^ n) (r : ℕ) (hr : n < r) (x : Fin r → X) :
    Shared.index S x < Shared.Phi n r := by
  have hg : Shared.growthFunction S n ≤ 2 ^ n := vc_growth_le S n _ (vc_index_le S)
  have h1 := vc_sauer S x n (fun e _ he => hn (le_antisymm hg (he ▸ vc_index_le_growth S _)))
  rw [vc_Phi_eq_sum, Finset.sum_range_succ]
  have : 0 < r.choose n := Nat.choose_pos hr.le
  omega

lemma vc_dichotomy {X : Type*} (S : Set (Set X)) (hS : S.Nonempty) :
    (∀ r : ℕ, Shared.growthFunction S r = 2 ^ r) ∨
      ∃ n : ℕ, 0 < n ∧ Shared.growthFunction S n ≠ 2 ^ n ∧
        (∀ r < n, Shared.growthFunction S r = 2 ^ r) ∧
        ∀ r : ℕ, Shared.growthFunction S r ≤ r ^ n + 1 := by
  by_cases hall : ∀ r : ℕ, Shared.growthFunction S r = 2 ^ r
  · exact Or.inl hall
  right
  push_neg at hall
  let n := Nat.find hall
  have hn : Shared.growthFunction S n ≠ 2 ^ n := Nat.find_spec hall
  have hmin : ∀ r < n, Shared.growthFunction S r = 2 ^ r := by
    intro r hr
    have := Nat.find_min hall hr
    push_neg at this
    exact this
  have h0 : Shared.growthFunction S 0 = 2 ^ 0 := by
    apply le_antisymm (vc_growth_le S 0 _ (vc_index_le S))
    refine le_trans ?_ (vc_index_le_growth S (Fin.elim0 : Fin 0 → X))
    rw [vc_index_eq, pow_zero, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos]
    refine ⟨∅, ?_⟩
    obtain ⟨A, hA⟩ := hS
    simp only [vcTraces, mem_filter, mem_univ, true_and]
    exact ⟨A, hA, fun i => i.elim0⟩
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (h ▸ h0) (h ▸ hn)
    · exact h
  refine ⟨n, hpos, hn, hmin, fun r => vc_growth_le S r _ (fun x => ?_)⟩
  rcases le_or_gt r n with hr | hr
  · exact (vc_index_le S x).trans (vc_two_pow_le n r hpos hr)
  · exact (vc_index_lt_phi S n hn r hr x).le.trans (vc_Phi_le n hpos r)

end VapnikChervonenkis.GrowthFunction

open VapnikChervonenkis.GrowthFunction
open VapnikChervonenkis VapnikChervonenkis.GrowthFunction

theorem solution {X : Type*} (S : Set (Set X)) (i n : ℕ) (x : Fin i → X)
    (hn1 : 1 ≤ n) (hni : n ≤ i) (hΔ : Shared.Phi n i ≤ Shared.index S x) :
    ∃ e : Fin n → Fin i, StrictMono e ∧ Shared.index S (x ∘ e) = 2 ^ n := by
  exact vc_lemma1 S i n x hn1 hni hΔ
