-- Prove2me | solution 1 for SatiationFisherNSW.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:21:14.642087+00:00
-- url     : https://prove2.me/submissions/b5829a46-916f-4f3c-bcd3-e1eb6bace1a8

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
open scoped Classical

open SatiationFisherNSW in
theorem solution
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p)
    (S : G → Option B) :
    (∏ i, I.val i S) ^ (1 / (Fintype.card B : ℝ)) ≤
      ((∏ i ∈ Finset.univ.filter (fun i => I.market.IsCapped x i), I.c i) *
        ∏ j ∈ Finset.univ.filter (fun j => 1 < p j), p j) ^ (1 / (Fintype.card B : ℝ)) := by
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
  -- part (e) of Lemma 4.3: money flowing into goods
  have he : ∀ j, p j * ∑ i, x i j = min (p j) 1 := by
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
  -- buyers in `B₀` are capped and spend nothing
  have hB0cap : ∀ i, I.market.InB0 p i → I.market.IsCapped x i := by
    intro i hi
    obtain ⟨j0, hj0, hpos0⟩ := hi
    obtain ⟨hdem, hthr, hmod⟩ := hbuy i
    obtain ⟨hx0, hbud, hopt⟩ := hdem
    have hne0 : I.market.u i j0 ≠ 0 := hpos0.ne'
    obtain ⟨z, hz⟩ : ∃ z : G → ℝ, z = fun j => if j = j0 then I.c i / I.market.u i j0 else 0 :=
      ⟨_, rfl⟩
    have hz0 : ∀ j, 0 ≤ z j := by
      intro j; rw [hz]; dsimp only
      split_ifs
      · exact div_nonneg (hcpos i).le (hu0 i j0)
      · exact le_refl 0
    have hzcost : ∑ j, p j * z j = 0 := by
      rw [hz]
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [hj0]
    have hzu : ∑ j, I.market.u i j * z j = I.c i := by
      rw [hz]
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      field_simp
    have h1 : min (I.c i) (∑ j, I.market.u i j * z j)
        ≤ min (I.c i) (∑ j, I.market.u i j * x i j) :=
      hopt z hz0 (by rw [hzcost]; show (0:ℝ) ≤ 1; norm_num)
    rw [hzu, min_self] at h1
    show min (I.c i) (∑ j, I.market.u i j * x i j) = I.c i
    exact le_antisymm (min_le_left _ _) h1
  have hB0spend : ∀ i, I.market.InB0 p i → ∑ j, p j * x i j = 0 := by
    intro i hi
    obtain ⟨hdem, hthr, hmod⟩ := hbuy i
    apply Finset.sum_eq_zero
    intro j _
    rcases (hdem.1 j).lt_or_eq with h | h
    · rw [hmbb_B0 i j hi (hthr j h), zero_mul]
    · rw [← h, mul_zero]
  -- spending of each buyer
  obtain ⟨sp, hsp⟩ : ∃ sp : B → ℝ, sp = fun i => ∑ j, p j * x i j := ⟨_, rfl⟩
  have hsp_unc : ∀ i, ¬ I.market.IsCapped x i →
      ¬ I.market.InB0 p i ∧ 1 < I.c i ∧ sp i = 1 := by
    intro i hi
    have hnb : ¬ I.market.InB0 p i := fun h => hi (hB0cap i h)
    obtain ⟨hs, hu, -⟩ := ha i hnb
    have hc1 : 1 < I.c i := by
      by_contra hle
      push_neg at hle
      apply hi
      show I.market.utility i (x i) = I.c i
      rw [hu, min_eq_right hle]
    refine ⟨hnb, hc1, ?_⟩
    rw [hsp]; dsimp only
    rw [hs, min_eq_left hc1.le]
  have hsp_cap : ∀ i, I.market.IsCapped x i → ¬ I.market.InB0 p i →
      I.c i ≤ 1 ∧ sp i = I.c i := by
    intro i hi hnb
    obtain ⟨hs, hu, hcc⟩ := ha i hnb
    have hc1 := hcc hi
    refine ⟨hc1, ?_⟩
    rw [hsp]; dsimp only
    rw [hs, min_eq_right hc1]
  have hmoney : ∑ j, min (p j) 1 = ∑ i, sp i := by
    rw [hsp]
    simp only
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← he j, Finset.mul_sum]
  -- valuations
  have hvu : ∀ i j, I.v i j = I.market.u i j := fun i j => (min_eq_left (hvc i j)).symm
  have hval_c : ∀ i, I.val i S ≤ I.c i := fun i => min_le_left _ _
  have hval_s : ∀ i, I.val i S ≤ ∑ j ∈ Finset.univ.filter (fun j => S j = some i), I.v i j :=
    fun i => min_le_right _ _
  have hval_nn : ∀ i, 0 ≤ I.val i S := by
    intro i
    apply le_min (hcpos i).le
    apply Finset.sum_nonneg
    intro j _
    rw [hvu]; exact hu0 i j
  -- the weights
  obtain ⟨m, hmdef⟩ : ∃ m : B → ℝ, m = fun i =>
      ∑ j ∈ Finset.univ.filter (fun j => S j = some i), min (p j) 1 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : B → ℝ, P = fun i =>
      ∏ j ∈ Finset.univ.filter (fun j => S j = some i ∧ 1 < p j), p j := ⟨_, rfl⟩
  have hP1 : ∀ i, 1 ≤ P i := by
    intro i
    rw [hPdef]; dsimp only
    calc (1:ℝ) = ∏ _j ∈ Finset.univ.filter (fun j => S j = some i ∧ 1 < p j), (1:ℝ) := by simp
      _ ≤ ∏ j ∈ Finset.univ.filter (fun j => S j = some i ∧ 1 < p j), p j := by
          apply Finset.prod_le_prod (fun j _ => zero_le_one)
          intro j hj
          exact (Finset.mem_filter.mp hj).2.2.le
  have hpP : ∀ i j, S j = some i → 1 < p j → p j ≤ P i := by
    intro i j hS hpj
    rw [hPdef]; dsimp only
    have hmem : j ∈ Finset.univ.filter (fun j => S j = some i ∧ 1 < p j) := by
      simp [hS, hpj]
    rw [← Finset.mul_prod_erase _ _ hmem]
    have h1 : 1 ≤ ∏ k ∈ (Finset.univ.filter (fun j => S j = some i ∧ 1 < p j)).erase j, p k := by
      calc (1:ℝ) = ∏ _k ∈ (Finset.univ.filter (fun j => S j = some i ∧ 1 < p j)).erase j,
            (1:ℝ) := by simp
        _ ≤ _ := by
            apply Finset.prod_le_prod (fun k _ => zero_le_one)
            intro k hk
            exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hk)).2.2.le
    nlinarith
  have hm0 : ∀ i, 0 ≤ m i := by
    intro i; rw [hmdef]; dsimp only
    exact Finset.sum_nonneg (fun j _ => le_min (hp0 j) zero_le_one)
  obtain ⟨w, hwdef⟩ : ∃ w : B → ℝ, w = fun i => if I.market.IsCapped x i then I.c i else P i :=
    ⟨_, rfl⟩
  have hw0 : ∀ i, 0 < w i := by
    intro i; rw [hwdef]; dsimp only
    split_ifs
    · exact hcpos i
    · linarith [hP1 i]
  -- bound on each ratio
  have hr : ∀ i, I.val i S / w i ≤ 1 + m i - sp i := by
    intro i
    rw [div_le_iff₀ (hw0 i)]
    by_cases hcap : I.market.IsCapped x i
    · have hwi : w i = I.c i := by rw [hwdef]; dsimp only; rw [if_pos hcap]
      rw [hwi]
      by_cases hb : I.market.InB0 p i
      · have hs0 : sp i = 0 := by rw [hsp]; exact hB0spend i hb
        rw [hs0]
        have := hval_c i
        have := hm0 i
        nlinarith [hcpos i]
      · obtain ⟨hc1, hsc⟩ := hsp_cap i hcap hb
        rw [hsc]
        have hvm : I.val i S ≤ m i := by
          refine le_trans (hval_s i) ?_
          rw [hmdef]; dsimp only
          apply Finset.sum_le_sum
          intro j _
          obtain ⟨hle, -⟩ := hratio i hb
          rw [hvu]
          exact le_min (hle j) (le_trans (huc i j) hc1)
        have hvc' := hval_c i
        have hcp := hcpos i
        by_cases hmc : I.c i ≤ m i
        · nlinarith
        · push_neg at hmc
          nlinarith
    · obtain ⟨hnb, hc1, hs1⟩ := hsp_unc i hcap
      have hwi : w i = P i := by rw [hwdef]; dsimp only; rw [if_neg hcap]
      rw [hwi, hs1]
      have hle := (hratio i hnb).1
      calc I.val i S ≤ ∑ j ∈ Finset.univ.filter (fun j => S j = some i), I.v i j := hval_s i
        _ ≤ ∑ j ∈ Finset.univ.filter (fun j => S j = some i), P i * min (p j) 1 := by
            apply Finset.sum_le_sum
            intro j hj
            have hSj := (Finset.mem_filter.mp hj).2
            rw [hvu]
            refine le_trans (hle j) ?_
            by_cases hpj : 1 < p j
            · rw [min_eq_right hpj.le, mul_one]
              exact hpP i j hSj hpj
            · push_neg at hpj
              rw [min_eq_left hpj]
              nlinarith [hP1 i, hp0 j]
        _ = (1 + m i - 1) * P i := by
            rw [← Finset.mul_sum]; simp only [hmdef]; ring
  -- sum of the bounds
  have hsum_m : ∑ i, m i ≤ ∑ j, min (p j) 1 := by
    rw [hmdef]
    simp only
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact le_min (hp0 j) zero_le_one
    · intro i _ i' _ hii'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro j hj hj'
      have h1 := (Finset.mem_filter.mp hj).2
      have h2 := (Finset.mem_filter.mp hj').2
      rw [h1] at h2
      exact hii' (Option.some_injective _ h2)
  have hrsum : ∑ i, I.val i S / w i ≤ (Fintype.card B : ℝ) := by
    calc ∑ i, I.val i S / w i ≤ ∑ i, (1 + m i - sp i) := Finset.sum_le_sum (fun i _ => hr i)
      _ = (Fintype.card B : ℝ) + ∑ i, m i - ∑ i, sp i := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          simp
      _ ≤ (Fintype.card B : ℝ) := by linarith [hsum_m, hmoney]
  -- product of ratios is at most one
  have hrprod : ∏ i, (I.val i S / w i) ≤ 1 := by
    calc ∏ i, (I.val i S / w i) ≤ ∏ i, Real.exp (I.val i S / w i - 1) := by
          apply Finset.prod_le_prod
          · intro i _; exact div_nonneg (hval_nn i) (hw0 i).le
          · intro i _
            linarith [Real.add_one_le_exp (I.val i S / w i - 1)]
      _ = Real.exp (∑ i, (I.val i S / w i - 1)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp 0 := by
          apply Real.exp_le_exp.2
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          linarith
      _ = 1 := Real.exp_zero
  -- product of the weights
  have hwprod : ∏ i, w i ≤ (∏ i ∈ Finset.univ.filter (fun i => I.market.IsCapped x i), I.c i) *
      ∏ j ∈ Finset.univ.filter (fun j => 1 < p j), p j := by
    have hsplit : ∏ i, w i = (∏ i ∈ Finset.univ.filter (fun i => I.market.IsCapped x i), I.c i) *
        ∏ i ∈ Finset.univ.filter (fun i => ¬ I.market.IsCapped x i), P i := by
      simp only [hwdef]
      rw [Finset.prod_ite]
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg (fun i _ => (hcpos i).le))
    rw [hPdef]
    simp only
    rw [← Finset.prod_biUnion]
    · have hsub : (Finset.univ.filter (fun i => ¬ I.market.IsCapped x i)).biUnion
          (fun i => Finset.univ.filter (fun j => S j = some i ∧ 1 < p j))
          ⊆ Finset.univ.filter (fun j => 1 < p j) := by
        intro j hj
        rw [Finset.mem_biUnion] at hj
        obtain ⟨i, _, hj⟩ := hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hj.2
      rw [← Finset.prod_sdiff hsub]
      have h1 : 1 ≤ ∏ j ∈ Finset.univ.filter (fun j => 1 < p j) \
          (Finset.univ.filter (fun i => ¬ I.market.IsCapped x i)).biUnion
          (fun i => Finset.univ.filter (fun j => S j = some i ∧ 1 < p j)), p j := by
        calc (1:ℝ) = ∏ _j ∈ Finset.univ.filter (fun j => 1 < p j) \
              (Finset.univ.filter (fun i => ¬ I.market.IsCapped x i)).biUnion
              (fun i => Finset.univ.filter (fun j => S j = some i ∧ 1 < p j)), (1:ℝ) := by simp
          _ ≤ _ := by
              apply Finset.prod_le_prod (fun k _ => zero_le_one)
              intro k hk
              exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk).1).2.le
      have h2 : 0 ≤ ∏ j ∈ (Finset.univ.filter (fun i => ¬ I.market.IsCapped x i)).biUnion
          (fun i => Finset.univ.filter (fun j => S j = some i ∧ 1 < p j)), p j :=
        Finset.prod_nonneg (fun j _ => hp0 j)
      nlinarith
    · intro i _ i' _ hii'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro j hj hj'
      have h1 := (Finset.mem_filter.mp hj).2.1
      have h2 := (Finset.mem_filter.mp hj').2.1
      rw [h1] at h2
      exact hii' (Option.some_injective _ h2)
  have hvalprod : ∏ i, I.val i S ≤ (∏ i ∈ Finset.univ.filter (fun i => I.market.IsCapped x i),
      I.c i) * ∏ j ∈ Finset.univ.filter (fun j => 1 < p j), p j := by
    have e : ∏ i, I.val i S = (∏ i, w i) * ∏ i, (I.val i S / w i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      field_simp [(hw0 i).ne']
    rw [e]
    have hw0' : 0 ≤ ∏ i, w i := Finset.prod_nonneg (fun i _ => (hw0 i).le)
    calc (∏ i, w i) * ∏ i, (I.val i S / w i) ≤ (∏ i, w i) * 1 :=
          mul_le_mul_of_nonneg_left hrprod hw0'
      _ = ∏ i, w i := mul_one _
      _ ≤ _ := hwprod
  exact Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => hval_nn i)) hvalprod (by positivity)
