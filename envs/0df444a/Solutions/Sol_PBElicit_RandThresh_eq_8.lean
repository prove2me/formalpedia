-- Prove2me | solution 1 for PBElicit.RandThresh.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:48:23.749996+00:00
-- url     : https://prove2.me/submissions/aabca35c-ccc5-4a84-ae39-98b2e8d6b55f

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

open Classical PBElicit.RandThresh

/-- A top set beats any set of no larger size inside the same ground set. -/
lemma pb8_top {A : Type*} [DecidableEq A] (S B Y : Finset A) (f : A → ℕ) (hB : B ⊆ S)
    (htop : ∀ a ∈ B, ∀ b ∈ S \ B, f b ≤ f a) (hY : Y ⊆ S) (hc : Y.card ≤ B.card) :
    ∑ a ∈ Y, f a ≤ ∑ a ∈ B, f a := by
  have e1 : ∑ a ∈ Y, f a = ∑ a ∈ Y \ B, f a + ∑ a ∈ Y ∩ B, f a := by
    rw [← Finset.sum_sdiff (Finset.inter_subset_left : Y ∩ B ⊆ Y), Finset.sdiff_inter_self_left]
  have e2 : ∑ a ∈ B, f a = ∑ a ∈ B \ Y, f a + ∑ a ∈ Y ∩ B, f a := by
    rw [← Finset.sum_sdiff (Finset.inter_subset_right : Y ∩ B ⊆ B), Finset.inter_comm,
      Finset.sdiff_inter_self_left]
  have hcard : (Y \ B).card ≤ (B \ Y).card := by
    have h1 := Finset.card_sdiff_add_card_inter Y B
    have h2 := Finset.card_sdiff_add_card_inter B Y
    rw [Finset.inter_comm] at h2
    omega
  rw [e1, e2]
  apply Nat.add_le_add_right
  rcases (B \ Y).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty] at hcard
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)]
    simp
  · obtain ⟨a0, ha0, hmin⟩ := Finset.exists_min_image (B \ Y) f hne
    have hle : ∀ b ∈ Y \ B, f b ≤ f a0 := by
      intro b hb
      have hb' := Finset.mem_sdiff.mp hb
      exact htop a0 (Finset.mem_sdiff.mp ha0).1 b
        (Finset.mem_sdiff.mpr ⟨hY hb'.1, hb'.2⟩)
    calc ∑ a ∈ Y \ B, f a ≤ (Y \ B).card • f a0 := Finset.sum_le_card_nsmul _ _ _ hle
      _ ≤ (B \ Y).card • f a0 := Nat.mul_le_mul_right _ hcard
      _ ≤ ∑ a ∈ B \ Y, f a := Finset.card_nsmul_le_sum _ _ _ hmin

lemma pb8_double {A : Type*} [DecidableEq A] (S B Y : Finset A) (f : A → ℕ) (hB : B ⊆ S)
    (htop : ∀ a ∈ B, ∀ b ∈ S \ B, f b ≤ f a) (hY : Y ⊆ S) (hc : Y.card ≤ 2 * B.card) :
    ∑ a ∈ Y, f a ≤ 2 * ∑ a ∈ B, f a := by
  obtain ⟨X, hXY, hXc⟩ := Finset.exists_subset_card_eq (min_le_right B.card Y.card)
  have h1 := pb8_top S B X f hB htop (hXY.trans hY) (by rw [hXc]; exact min_le_left _ _)
  have hcd : (Y \ X).card ≤ B.card := by
    rw [Finset.card_sdiff_of_subset hXY, hXc]; omega
  have h2 := pb8_top S B (Y \ X) f hB htop (Finset.sdiff_subset.trans hY) hcd
  rw [← Finset.sum_sdiff hXY]
  omega

lemma pb8_mem_bucket {A : Type*} [Fintype A] (c : A → ℝ) (m j : ℕ) (a : A) :
    a ∈ bucket c m j ↔ c a ∈ Ivl m j := by
  simp [bucket]

theorem solution {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc0 : ∀ a, 0 ≤ c a) (v : Fin n → A → ℝ) (hv : IsUtilityProfile v) (m K : ℕ)
    (hA : Fintype.card A = m) (hmK : m = 2 ^ K) (Sstar : Finset A)
    (hS : IsWelfareOptimal c v Sstar)
    (j k : ℕ) (hj : j ∈ Finset.Icc 1 (2 * K)) (hk : k ∈ Finset.Icc 1 (2 * K)) (B : Finset A)
    (hB : IsGreedyTop v c m j k B) :
    (1 / 4 : ℝ) * (cntStar v c m Sstar j k : ℝ) * up m j ≤ sw v B := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hj0 : j ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  set Y := Sstar ∩ bucket c m k with hYdef
  set t := lo m j with ht
  set f : A → ℕ := fun a => approvalCount v t a with hf
  have hm2 : (m:ℝ)^2 = 2 ^ (2 * K) := by rw [hmK]; push_cast; rw [← pow_mul, mul_comm]
  have hmpos : (0:ℝ) < (m:ℝ)^2 := by rw [hm2]; positivity
  -- step 1: n*_{jk} ≤ Σ_Y approvals at ℓ_j
  have hstep1 : cntStar v c m Sstar j k ≤ ∑ a ∈ Y, f a := by
    unfold cntStar
    refine Finset.sum_le_sum (fun a _ => ?_)
    unfold cnt
    simp only [hf, approvalCount]
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simp only [Ivl, hj0, if_false, Set.mem_Ioc] at hi
    exact hi.1.le
  -- step 2: |Y| ≤ 2|B|
  have hYS : Y ⊆ bucket c m k := Finset.inter_subset_right
  have hcardY : Y.card ≤ 2 * B.card := by
    rw [hB.2.1]
    rcases le_total (m ^ 2 / 2 ^ k) (bucket c m k).card with hle | hle
    · rw [min_eq_left hle]
      -- each a ∈ Y has c a > 2^{k-1}/m²
      have hcost : ∑ a ∈ Y, c a ≤ 1 :=
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
          (fun a _ _ => hc0 a)).trans hS.1.1
      have hlow := Finset.card_nsmul_le_sum Y c (lo m k) (fun a ha => by
        have := (pb8_mem_bucket c m k a).mp (hYS ha)
        simp only [Ivl, hk0, if_false, Set.mem_Ioc] at this
        exact this.1.le)
      rw [nsmul_eq_mul] at hlow
      simp only [lo, hk0, if_false] at hlow
      have hYr : (Y.card : ℝ) * 2 ^ (k - 1) ≤ (m:ℝ)^2 := by
        have := hlow.trans hcost
        rw [mul_div_assoc', div_le_one hmpos] at this; exact this
      have hpow : (2:ℕ) ^ k * 2 ^ (2 * K - k) = m ^ 2 := by
        rw [← pow_add, hmK, ← pow_mul, mul_comm K 2]; congr 1; omega
      have hdiv : m ^ 2 / 2 ^ k = 2 ^ (2 * K - k) := by
        rw [← hpow, Nat.mul_div_cancel_left _ (by positivity)]
      rw [hdiv]
      have hYn : Y.card * 2 ^ (k - 1) ≤ 2 ^ (k - 1) * (2 * 2 ^ (2 * K - k)) := by
        have h' : (m:ℝ)^2 = ((2 ^ (k-1) * (2 * 2 ^ (2 * K - k)) : ℕ) : ℝ) := by
          push_cast
          rw [hm2, ← mul_assoc, ← pow_succ, ← pow_add]; congr 1; omega
        rw [h'] at hYr
        exact_mod_cast hYr
      rw [mul_comm (2 ^ (k-1))] at hYn
      exact Nat.le_of_mul_le_mul_right hYn (by positivity)
    · rw [min_eq_right hle]
      have := Finset.card_le_card hYS
      omega
  have hstep2 : ∑ a ∈ Y, f a ≤ 2 * ∑ a ∈ B, f a :=
    pb8_double (bucket c m k) B Y f hB.1 hB.2.2 hYS hcardY
  -- step 3: sw(B) ≥ ℓ_j Σ_B approvals
  have htpos : 0 ≤ t := by rw [ht]; unfold lo; split_ifs <;> positivity
  have hstep3 : t * (∑ a ∈ B, f a : ℕ) ≤ sw v B := by
    unfold sw
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    simp only [hf, approvalCount]
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    split_ifs with h
    · simpa using h
    · simpa using hv.1 i a
  have hut : up m j = 2 * t := by
    rw [ht]; simp only [up, lo, hj0, if_false]
    rw [show j = (j - 1) + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring
  have h1 : (cntStar v c m Sstar j k : ℝ) ≤ 2 * ((∑ a ∈ B, f a : ℕ) : ℝ) := by
    have := hstep1.trans hstep2
    exact_mod_cast this
  rw [hut]
  nlinarith
