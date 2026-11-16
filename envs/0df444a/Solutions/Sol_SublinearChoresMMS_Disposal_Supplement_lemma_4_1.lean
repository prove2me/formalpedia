-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.Supplement.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:22:07.126489+00:00
-- url     : https://prove2.me/submissions/e573d765-4db5-4de8-8638-f215ff67aad6

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Supplement_FixedBundles

open SublinearChoresMMS.Disposal SublinearChoresMMS.Disposal.Supplement
open Finset

theorem SCM41_goodPartition (n m : ℕ) (hn : 0 < n) (u : Fin m → ℝ)
    (hmu : costShare u n = 1) :
    ∃ f : Fin m → Fin n, ∀ b, ∑ e ∈ univ.filter (fun g => f g = b), u e ≤ 1 := by
  classical
  unfold costShare LittleCharity.MMS.mms at hmu
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := fun f : Fin m → Fin n =>
    ⨅ j : Fin n, -∑ e ∈ (univ : Finset (Fin m)).filter (fun g => f g = j), u e)
  refine ⟨f, fun b => ?_⟩
  have h1 : (⨅ j : Fin n, -∑ e ∈ (univ : Finset (Fin m)).filter (fun g => f g = j), u e) = -1 := by
    rw [hf]; linarith
  have h2 := ciInf_le (Set.finite_range (fun j : Fin n =>
    -∑ e ∈ (univ : Finset (Fin m)).filter (fun g => f g = j), u e)).bddBelow b
  rw [h1] at h2
  linarith

theorem SCM41_count {n m : ℕ} (f : Fin m → Fin n) (T : Finset (Fin m)) (g : Fin n → ℕ)
    (hg : ∀ b, (T.filter (fun t => f t = b)).card ≤ g b) : T.card ≤ ∑ b, g b := by
  classical
  rw [card_eq_sum_card_fiberwise (f := f) (t := univ) (fun _ _ => mem_univ _)]
  exact sum_le_sum (fun b _ => hg b)

theorem SCM41_prefix (m N : ℕ) (h : N ≤ m) :
    ((univ : Finset (Fin m)).filter (fun t => t.val < N)).card = N := by
  have : (univ : Finset (Fin m)).filter (fun t => t.val < N) =
      (univ : Finset (Fin N)).map ⟨Fin.castLE h, Fin.castLE_injective h⟩ := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro ht; exact ⟨⟨t.val, ht⟩, Fin.ext (by simp [Fin.coe_castLE])⟩
    · rintro ⟨a, rfl⟩; simp [Fin.coe_castLE]
  rw [this, card_map, card_univ, Fintype.card_fin]

theorem SCM41_three {m : ℕ} (u : Fin m → ℝ) (hpos : ∀ e, 0 < u e) (B S : Finset (Fin m))
    (hSB : S ⊆ B) (hB : ∑ e ∈ B, u e ≤ 1) (x : ℝ) (hx : 1 / 3 < x)
    (hS : ∀ e ∈ S, x ≤ u e) : S.card ≤ 2 := by
  by_contra hc
  push Not at hc
  have h1 : (S.card : ℝ) * x ≤ ∑ e ∈ S, u e := by
    have := card_nsmul_le_sum S u x hS
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ e ∈ S, u e ≤ ∑ e ∈ B, u e :=
    sum_le_sum_of_subset_of_nonneg hSB (fun e _ _ => (hpos e).le)
  have h3 : (3 : ℝ) ≤ S.card := by exact_mod_cast hc
  nlinarith

theorem solution (n m : ℕ) (hn : 0 < n) (hm : 2 * n ≤ m)
    (c : Cost n m) (hc : Normalized c) :
    (∀ i e, e ∈ oppositeTail n m → c i e ≤ (1 / 3 : ℝ)) ∧
    ∀ i j, cost c i (oppositePairs n m j) ≤ (4 / 3 : ℝ) := by
  classical
  obtain ⟨hpos, hanti, hmu⟩ := hc
  constructor
  · intro i e he
    have he2 : 2 * n ≤ e.val := by
      unfold oppositeTail at he; simpa using he
    obtain ⟨f, hf⟩ := SCM41_goodPartition n m hn (c i) (hmu i)
    by_contra hgt
    push Not at hgt
    set T := (univ : Finset (Fin m)).filter (fun t => t.val < 2 * n + 1) with hTdef
    have hTc : T.card = 2 * n + 1 := SCM41_prefix m _ (by omega)
    have hT : ∀ t ∈ T, t.val < 2 * n + 1 := fun t ht => (mem_filter.mp ht).2
    have hTge : ∀ t ∈ T, c i e ≤ c i t := by
      intro t ht
      apply (hanti i).antitone
      rw [Fin.le_def]; have := hT t ht; omega
    have hcount := SCM41_count f T (fun _ => 2) (fun b =>
      SCM41_three (c i) (hpos i) _ _ (fun t ht => by
        simp only [mem_filter] at ht ⊢; exact ⟨mem_univ _, ht.2⟩) (hf b) (c i e) hgt
        (fun t ht => hTge t (mem_filter.mp ht).1))
    simp at hcount
    omega
  · intro i j
    obtain ⟨f, hf⟩ := SCM41_goodPartition n m hn (c i) (hmu i)
    have hj : j.val < n := j.2
    set j' : Fin m := ⟨j.val, by omega⟩ with hj'
    set k' : Fin m := ⟨2 * n - 1 - j.val, by omega⟩ with hk'
    have hne : j' ≠ k' := by
      intro h; have := congrArg Fin.val h; simp [hj', hk'] at this; omega
    have hpair : oppositePairs n m j = {j', k'} := by
      ext e
      simp only [oppositePairs, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro (h | h)
        · left; ext; simp [hj', h]
        · right; ext; simp [hk', h]
      · rintro (h | h)
        · left; rw [h]
        · right; rw [h]
    unfold cost ChoresEFX.cost
    rw [hpair, sum_pair hne]
    -- c j' ≤ 1
    have hbundle : ∀ t : Fin m, ∀ S : Finset (Fin m), S ⊆ univ.filter (fun g => f g = f t) →
        ∑ e ∈ S, c i e ≤ 1 := by
      intro t S hS
      exact (sum_le_sum_of_subset_of_nonneg hS (fun e _ _ => (hpos i e).le)).trans (hf (f t))
    have hj1 : c i j' ≤ 1 := by
      have := hbundle j' {j'} (by intro x hx; simp at hx; simp [hx])
      simpa using this
    by_contra hgt
    push Not at hgt
    have hk3 : 1 / 3 < c i k' := by linarith
    set T := (univ : Finset (Fin m)).filter (fun t => t.val < 2 * n - j.val) with hTdef
    have hTc : T.card = 2 * n - j.val := SCM41_prefix m _ (by omega)
    have hT : ∀ t ∈ T, t.val < 2 * n - j.val := fun t ht => (mem_filter.mp ht).2
    set L := (univ : Finset (Fin m)).filter (fun t => t.val < j.val + 1) with hLdef
    have hLc : L.card = j.val + 1 := SCM41_prefix m _ (by omega)
    have hL : ∀ t ∈ L, t.val < j.val + 1 := fun t ht => (mem_filter.mp ht).2
    have hLT : ∀ t ∈ L, t ∈ T := by
      intro t ht; have := hL t ht; simp only [hTdef, mem_filter, mem_univ, true_and]; omega
    have hTge : ∀ t ∈ T, c i k' ≤ c i t := by
      intro t ht
      apply (hanti i).antitone
      rw [Fin.le_def]; have := hT t ht; simp [hk']; omega
    have hLge : ∀ t ∈ L, c i j' ≤ c i t := by
      intro t ht
      apply (hanti i).antitone
      rw [Fin.le_def]; have := hL t ht; simp [hj']; omega
    -- a chore of L is alone among T in its bundle
    have halone : ∀ t0 ∈ L, ∀ t ∈ T, t ≠ t0 → f t ≠ f t0 := by
      intro t0 ht0 t ht hne' hft
      have := hbundle t0 {t0, t} (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [hft])
      rw [sum_pair (Ne.symm hne')] at this
      have := hLge t0 ht0
      have := hTge t ht
      linarith
    have hinj : Set.InjOn f L := by
      intro a ha b hb hab
      by_contra hne'
      exact halone a ha b (hLT b hb) (Ne.symm hne') hab.symm
    set img := L.image f with himg
    have himgc : img.card = j.val + 1 := by rw [himg, card_image_of_injOn hinj, hLc]
    have hcount := SCM41_count f T (fun b => if b ∈ img then 1 else 2) (fun b => by
      split_ifs with hb
      · obtain ⟨t0, ht0, hft0⟩ := mem_image.mp hb
        have hsub : T.filter (fun t => f t = b) ⊆ {t0} := by
          intro t ht
          rw [mem_filter] at ht
          rw [mem_singleton]
          by_contra hne'
          exact halone t0 ht0 t ht.1 hne' (ht.2.trans hft0.symm)
        simpa using card_le_card hsub
      · exact SCM41_three (c i) (hpos i) _ _ (fun t ht => by
          simp only [mem_filter] at ht ⊢; exact ⟨mem_univ _, ht.2⟩) (hf b) (c i k') hk3
          (fun t ht => hTge t (mem_filter.mp ht).1))
    have hsum : ∑ b : Fin n, (if b ∈ img then 1 else 2) + img.card = 2 * n := by
      have h1 : ∑ b : Fin n, (if b ∈ img then (1:ℕ) else 0) = img.card := by
        rw [sum_ite_mem, univ_inter, sum_const, smul_eq_mul, mul_one]
      rw [← h1, ← sum_add_distrib]
      have : ∀ b : Fin n, ((if b ∈ img then 1 else 2) + (if b ∈ img then 1 else 0) : ℕ) = 2 := by
        intro b; split_ifs <;> rfl
      simp only [this, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    omega
