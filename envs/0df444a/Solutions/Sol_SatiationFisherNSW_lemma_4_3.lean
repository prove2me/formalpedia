-- Prove2me | solution 1 for SatiationFisherNSW.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:15:56.599073+00:00
-- url     : https://prove2.me/submissions/d471fc80-c263-4bab-bb91-81db1b05515d

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
open scoped Classical

open SatiationFisherNSW in
theorem solution
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p) :
    (∀ i, ¬ I.market.InB0 p i →
      ∑ j, p j * x i j = min 1 (I.c i) ∧ I.market.utility i (x i) = min 1 (I.c i) ∧
        (I.market.IsCapped x i → I.c i ≤ 1)) ∧
    (∀ i, I.market.IsCapped x i → 1 ≤ ∑ j, x i j) ∧
    (∀ i j, I.market.IsCapped x i → I.market.IsMBB p i j → p j ≤ 1) ∧
    (∀ j, 0 < p j → p j < 1 → ∑ i, x i j = 1) ∧
    (∀ j, p j * ∑ i, x i j = min (p j) 1) := by
  obtain ⟨hp0, hsup, hbuy, hcs⟩ := hEq
  have hc : ∀ i, I.market.c i = I.c i := fun i => rfl
  have hm : ∀ i, I.market.m i = 1 := fun i => rfl
  have hd : ∀ j, I.market.d j = 1 := fun j => rfl
  have hes : ∀ j, I.market.modestSupply p j = if p j = 0 then 1 else min 1 (1 / p j) := by
    intro j
    unfold FisherMarket.modestSupply
    rw [hd]
  have hu0 : ∀ i j, 0 ≤ I.market.u i j := I.market.u_nonneg
  have huc : ∀ i j, I.market.u i j ≤ I.c i := fun i j => min_le_right _ _
  have hcpos := I.c_pos
  -- ratio facts for buyers outside `B₀`
  have hratio : ∀ i, ¬ I.market.InB0 p i →
      (∀ k, I.market.u i k ≤ p k) ∧ (∃ k, 0 < p k ∧ I.market.u i k = p k) := by
    intro i hi
    have hn := hN i hi
    unfold FisherMarket.mbbRatio at hn
    have hbdd : BddAbove (Set.range fun k => I.market.u i k / p k) :=
      (Set.finite_range _).bddAbove
    rcases isEmpty_or_nonempty G with hG | hG
    · exfalso
      rw [Real.iSup_of_isEmpty] at hn
      norm_num at hn
    constructor
    · intro k
      have h1 : I.market.u i k / p k ≤ 1 := by
        rw [← hn]
        exact le_ciSup hbdd k
      by_cases hpk : p k = 0
      · have hnot : ¬ (0 < I.market.u i k) := fun h => hi ⟨k, hpk, h⟩
        have h2 := hu0 i k
        rw [hpk]
        linarith [not_lt.mp hnot]
      · have hpk' : 0 < p k := lt_of_le_of_ne (hp0 k) (Ne.symm hpk)
        rwa [div_le_one hpk'] at h1
    · obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => I.market.u i k / p k)
      rw [hn] at hk
      have hpk : p k ≠ 0 := by
        intro h
        rw [h, div_zero] at hk
        norm_num at hk
      have hpk' : 0 < p k := lt_of_le_of_ne (hp0 k) (Ne.symm hpk)
      refine ⟨k, hpk', ?_⟩
      rwa [div_eq_one_iff_eq hpk] at hk
  -- MBB goods of a buyer outside `B₀` satisfy `u = p > 0`
  have hmbb_eq : ∀ i j, ¬ I.market.InB0 p i → I.market.IsMBB p i j →
      I.market.u i j = p j ∧ 0 < p j := by
    intro i j hi hmbb
    obtain ⟨hle, k, hpk, hk⟩ := hratio i hi
    obtain ⟨hpos, hcmp⟩ := hmbb
    have hpj : 0 < p j := by
      rcases (hp0 j).lt_or_eq with h | h
      · exact h
      · exact absurd ⟨j, h.symm, hpos⟩ hi
    have h1 := hcmp k
    rw [hk] at h1
    have h2 : p j ≤ I.market.u i j := by nlinarith
    exact ⟨le_antisymm (hle j) h2, hpj⟩
  -- MBB goods of a buyer in `B₀` have price zero
  have hmbb_B0 : ∀ i j, I.market.InB0 p i → I.market.IsMBB p i j → p j = 0 := by
    intro i j hi hmbb
    obtain ⟨j0, hj0, hpos0⟩ := hi
    obtain ⟨hpos, hcmp⟩ := hmbb
    have h1 := hcmp j0
    rw [hj0, mul_zero] at h1
    have := hp0 j
    nlinarith
  -- part (a)
  have ha : ∀ i, ¬ I.market.InB0 p i →
      ∑ j, p j * x i j = min 1 (I.c i) ∧ I.market.utility i (x i) = min 1 (I.c i) ∧
        (I.market.IsCapped x i → I.c i ≤ 1) := by
    intro i hi
    obtain ⟨hdem, hthr, hmod⟩ := hbuy i
    obtain ⟨hx0, hbud, hopt⟩ := hdem
    obtain ⟨hle, k, hpk, hk⟩ := hratio i hi
    have hTS : ∑ j, I.market.u i j * x i j = ∑ j, p j * x i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rcases (hx0 j).lt_or_eq with h | h
      · rw [(hmbb_eq i j hi (hthr j h)).1]
      · rw [← h]; simp
    rw [hm] at hbud
    obtain ⟨z, hz⟩ : ∃ z : G → ℝ, z = fun j => if j = k then 1 / p k else 0 := ⟨_, rfl⟩
    have hz0 : ∀ j, 0 ≤ z j := by
      intro j; rw [hz]; dsimp only; split_ifs <;> positivity
    have hzcost : ∑ j, p j * z j = 1 := by
      rw [hz]
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [hpk.ne']
    have hzu : ∑ j, I.market.u i j * z j = 1 := by
      rw [hz]
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [hk, hpk.ne']
    have hopt' := hopt z hz0 (by rw [hzcost, hm])
    have hT : ∑ j, I.market.u i j * x i j ≤ I.c i := hmod
    unfold FisherMarket.utility at hopt'
    rw [hzu] at hopt'
    try rw [hc] at hopt'
    obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ∑ j, I.market.u i j * x i j := ⟨_, rfl⟩
    rw [← hTdef] at hopt' hT
    rw [← hTdef] at hTS
    have hT1 : T ≤ 1 := by rw [hTS]; exact hbud
    have hmin : min (I.c i) T = T := min_eq_right hT
    rw [hmin] at hopt'
    have hTeq : T = min 1 (I.c i) := by
      apply le_antisymm (le_min hT1 hT)
      rw [min_comm]
      exact hopt'
    have hutil : I.market.utility i (x i) = min 1 (I.c i) := by
      unfold FisherMarket.utility
      try rw [hc]
      rw [← hTdef, hmin, hTeq]
    refine ⟨by rw [← hTS, hTeq], hutil, ?_⟩
    intro hcap
    unfold FisherMarket.IsCapped at hcap
    rw [hutil] at hcap
    try rw [hc] at hcap
    rw [← hcap]
    exact min_le_left _ _
  refine ⟨ha, ?_, ?_, ?_, ?_⟩
  · -- part (b)
    intro i hcap
    obtain ⟨hdem, hthr, hmod⟩ := hbuy i
    have hx0 := hdem.1
    unfold FisherMarket.IsCapped FisherMarket.utility at hcap
    try rw [hc] at hcap
    have h1 : I.c i ≤ ∑ j, I.market.u i j * x i j := min_eq_left_iff.mp hcap
    have h2 : ∑ j, I.market.u i j * x i j ≤ I.c i * ∑ j, x i j := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (huc i j) (hx0 j))
    have h3 : I.c i * 1 ≤ I.c i * ∑ j, x i j := by linarith
    exact le_of_mul_le_mul_left h3 (hcpos i)
  · -- part (c)
    intro i j hcap hmbb
    by_cases hB0 : I.market.InB0 p i
    · rw [hmbb_B0 i j hB0 hmbb]; norm_num
    · obtain ⟨h1, h2⟩ := hmbb_eq i j hB0 hmbb
      have h3 := (ha i hB0).2.2 hcap
      have h4 := huc i j
      linarith
  · -- part (d)
    intro j hpj hpj1
    have h := hcs j
    rcases mul_eq_zero.mp h with h' | h'
    · linarith
    · rw [hes, if_neg hpj.ne', min_eq_left (le_of_lt (one_lt_one_div hpj hpj1))] at h'
      linarith
  · -- part (e)
    intro j
    rcases (hp0 j).lt_or_eq with hpj | hpj
    · have h := hcs j
      rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · have hsum : ∑ i, x i j = min 1 (1 / p j) := by
          rw [hes, if_neg hpj.ne'] at h'
          linarith
        rw [hsum, mul_min_of_nonneg _ _ hpj.le, mul_one, mul_one_div_cancel hpj.ne', min_comm]
    · rw [← hpj, zero_mul]
      exact (min_eq_left zero_le_one).symm
