-- Prove2me | solution 1 for PBElicit.RandThresh.mechanism_A_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:50:55.875949+00:00
-- url     : https://prove2.me/submissions/95ec0c3f-a452-49fb-b280-3163ded472ad

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting
import Theorems.Thm_PBElicit_RandThresh_eq_7
import Theorems.Thm_PBElicit_RandThresh_eq_8

open Classical PBElicit.RandThresh

lemma pb6_dyad (L : ℕ) (y : ℝ) (h1 : 1 < y) (h2 : y ≤ 2 ^ L) :
    ∃ j ∈ Finset.Icc 1 L, (2:ℝ) ^ (j - 1) < y ∧ y ≤ 2 ^ j := by
  induction L with
  | zero => simp at h2; linarith
  | succ L ih =>
    by_cases h : y ≤ 2 ^ L
    · obtain ⟨j, hj, hj'⟩ := ih h
      exact ⟨j, by simp only [Finset.mem_Icc] at hj ⊢; omega, hj'⟩
    · exact ⟨L + 1, by simp, by simpa using (not_le.mp h), h2⟩

lemma pb6_mem_ivl (m j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    x ∈ Ivl m j ↔ lo m j < x ∧ x ≤ up m j := by
  have : j ≠ 0 := by omega
  simp [Ivl, this]

lemma pb6_cover (m K : ℕ) (hmK : m = 2 ^ K) (x : ℝ) (hx1 : 1 / (m:ℝ)^2 < x) (hx2 : x ≤ 1) :
    ∃ j ∈ Finset.Icc 1 (2 * K), x ∈ Ivl m j := by
  have hm2 : (m:ℝ)^2 = 2 ^ (2 * K) := by rw [hmK]; push_cast; rw [← pow_mul, mul_comm]
  have hmpos : (0:ℝ) < (m:ℝ)^2 := by rw [hm2]; positivity
  obtain ⟨j, hj, h1, h2⟩ := pb6_dyad (2 * K) (x * (m:ℝ)^2)
    (by rw [div_lt_iff₀ hmpos] at hx1; linarith)
    (by rw [← hm2]; nlinarith)
  refine ⟨j, hj, ?_⟩
  rw [pb6_mem_ivl m j (Finset.mem_Icc.mp hj).1]
  have hj1 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  simp only [lo, up, hj1, if_false]
  constructor
  · rw [div_lt_iff₀ hmpos]; exact h1
  · rw [le_div_iff₀ hmpos]; exact h2

lemma pb6_disj (m j j' : ℕ) (hm : 0 < m) (hj : 1 ≤ j) (hjj : j < j') (x : ℝ)
    (h : x ∈ Ivl m j) (h' : x ∈ Ivl m j') : False := by
  rw [pb6_mem_ivl m j hj] at h
  rw [pb6_mem_ivl m j' (by omega)] at h'
  have hj1 : j' ≠ 0 := by omega
  have : up m j ≤ lo m j' := by
    simp only [up, lo, hj1, if_false]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith [h.2, h'.1]

lemma pbA_mem_bucket {A : Type*} [Fintype A] (c : A → ℝ) (m j : ℕ) (a : A) :
    a ∈ bucket c m j ↔ c a ∈ Ivl m j := by
  simp [bucket]

theorem solution {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc0 : ∀ a, 0 ≤ c a) (v : Fin n → A → ℝ) (hv : IsUtilityProfile v) (m K : ℕ) (hK : 1 ≤ K)
    (hA : Fintype.card A = m) (hmK : m = 2 ^ K) (Sstar : Finset A)
    (hS : IsWelfareOptimal c v Sstar)
    (B : ℕ → ℕ → Finset A)
    (hB : ∀ j ∈ Finset.Icc 1 (2 * K), ∀ k ∈ Finset.Icc 1 (2 * K), IsGreedyTop v c m j k (B j k)) :
    1 / (16 * Real.logb 2 m ^ 2) * (sw v (Sstar \ bucket c m 0) - (n : ℝ) / m)
      ≤ 1 / (2 * Real.logb 2 m) ^ 2 *
          ∑ j ∈ Finset.Icc 1 (2 * K), ∑ k ∈ Finset.Icc 1 (2 * K), sw v (B j k) := by
  have hm : 0 < m := by rw [hmK]; positivity
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hm2pos : (0:ℝ) < (m:ℝ)^2 := by positivity
  have hlog : Real.logb 2 (m:ℝ) = K := by
    rw [hmK]; push_cast; rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [hlog]
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hv0 := hv.1
  have hswnn : ∀ S : Finset A, 0 ≤ sw v S := fun S =>
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun i _ => hv0 i a))
  set I := Finset.Icc 1 (2 * K) with hI
  -- each element of S* has cost ≤ 1
  have hc1 : ∀ a ∈ Sstar, c a ≤ 1 := by
    intro a ha
    exact (Finset.single_le_sum (f := c) (fun b _ => hc0 b) ha).trans hS.1.1
  -- (a) cover of S* \ S_0 by the buckets S_k, k ∈ [1, 2K]
  have hcover : sw v (Sstar \ bucket c m 0) ≤ ∑ k ∈ I, sw v (Sstar ∩ bucket c m k) := by
    unfold sw
    set g : A → ℝ := fun a => ∑ i, v i a
    have hg : ∀ a, 0 ≤ g a := fun a => Finset.sum_nonneg (fun i _ => hv0 i a)
    calc ∑ a ∈ Sstar \ bucket c m 0, g a
        ≤ ∑ a ∈ Sstar \ bucket c m 0, ∑ k ∈ I, (if a ∈ bucket c m k then g a else 0) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          obtain ⟨haS, ha0⟩ := Finset.mem_sdiff.mp ha
          rw [pbA_mem_bucket] at ha0
          have ha0' : 1 / (m:ℝ)^2 < c a := by
            by_contra hh
            exact ha0 (by
              rw [show Ivl m 0 = Set.Icc 0 (1 / (m:ℝ)^2) by simp [Ivl]]
              exact ⟨hc0 a, not_lt.mp hh⟩)
          obtain ⟨k, hk, hck⟩ := pb6_cover m K hmK (c a) ha0' (hc1 a haS)
          have := Finset.single_le_sum (f := fun k => if a ∈ bucket c m k then g a else 0)
            (fun j _ => by split_ifs <;> simp [hg]) hk
          simp only [if_pos ((pbA_mem_bucket c m k a).mpr hck)] at this
          exact this
      _ = ∑ k ∈ I, ∑ a ∈ (Sstar \ bucket c m 0).filter (fun a => a ∈ bucket c m k), g a := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          exact (Finset.sum_filter _ _).symm
      _ ≤ ∑ k ∈ I, ∑ a ∈ Sstar ∩ bucket c m k, g a := by
          refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun a _ _ => hg a))
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_sdiff] at ha
          exact Finset.mem_inter.mpr ⟨ha.1.1, ha.2⟩
  -- (b) the buckets are disjoint, so Σ_k |S* ∩ S_k| ≤ m
  have hcardsum : ∑ k ∈ I, ((Sstar ∩ bucket c m k).card : ℝ) ≤ m := by
    have h1 : ∑ k ∈ I, (Sstar ∩ bucket c m k).card
        = ∑ a ∈ Sstar, (I.filter (fun k => a ∈ bucket c m k)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_filter]
      congr 1
    have h2 : ∀ a ∈ Sstar, (I.filter (fun k => a ∈ bucket c m k)).card ≤ 1 := by
      intro a _
      rw [Finset.card_le_one]
      intro k hk k' hk'
      simp only [Finset.mem_filter, hI, Finset.mem_Icc, pbA_mem_bucket] at hk hk'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact pb6_disj m k k' hm hk.1.1 hlt (c a) hk.2 hk'.2
      · exact pb6_disj m k' k hm hk'.1.1 hgt (c a) hk'.2 hk.2
    have h3 : ∑ k ∈ I, (Sstar ∩ bucket c m k).card ≤ m := by
      rw [h1]
      calc ∑ a ∈ Sstar, (I.filter (fun k => a ∈ bucket c m k)).card ≤ ∑ a ∈ Sstar, 1 :=
            Finset.sum_le_sum h2
        _ = Sstar.card := by simp
        _ ≤ m := by rw [← hA]; exact Finset.card_le_univ _
    exact_mod_cast h3
  -- (c) Eq. (7) and Eq. (8)
  have h7 : ∀ k ∈ I, sw v (Sstar ∩ bucket c m k)
      ≤ ((Sstar ∩ bucket c m k).card : ℝ) * ((n : ℝ) / (m : ℝ) ^ 2)
        + ∑ j ∈ I, 4 * sw v (B j k) := by
    intro k hk
    have e7 := (eq_7 c v hv m K hA hmK Sstar hS k (Finset.mem_Icc.mp hk).2).2
    have e8 : ∑ j ∈ I, (cntStar v c m Sstar j k : ℝ) * up m j ≤ ∑ j ∈ I, 4 * sw v (B j k) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have := eq_8 c hc0 v hv m K hA hmK Sstar hS j k hj hk (B j k) (hB j hj k hk)
      linarith
    linarith
  have hX : sw v (Sstar \ bucket c m 0) ≤ (n:ℝ) / m
      + 4 * ∑ j ∈ I, ∑ k ∈ I, sw v (B j k) := by
    have hsum := Finset.sum_le_sum h7
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    have hlow : (∑ k ∈ I, ((Sstar ∩ bucket c m k).card : ℝ)) * ((n : ℝ) / (m : ℝ) ^ 2)
        ≤ (n:ℝ) / m := by
      calc (∑ k ∈ I, ((Sstar ∩ bucket c m k).card : ℝ)) * ((n : ℝ) / (m : ℝ) ^ 2)
          ≤ (m:ℝ) * ((n : ℝ) / (m : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcardsum (by positivity)
        _ = (n:ℝ) / m := by field_simp
    have hcomm : ∑ k ∈ I, ∑ j ∈ I, 4 * sw v (B j k) = 4 * ∑ j ∈ I, ∑ k ∈ I, sw v (B j k) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
    linarith
  have hfinal : 1 / (16 * (K:ℝ) ^ 2) * (sw v (Sstar \ bucket c m 0) - (n : ℝ) / m)
      ≤ 1 / (16 * (K:ℝ) ^ 2) * (4 * ∑ j ∈ I, ∑ k ∈ I, sw v (B j k)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have heq : 1 / (16 * (K:ℝ) ^ 2) * (4 * ∑ j ∈ I, ∑ k ∈ I, sw v (B j k))
      = 1 / (2 * (K:ℝ)) ^ 2 * ∑ j ∈ I, ∑ k ∈ I, sw v (B j k) := by
    field_simp; ring
  linarith
