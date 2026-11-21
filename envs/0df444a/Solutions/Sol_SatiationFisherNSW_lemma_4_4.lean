-- Prove2me | solution 1 for SatiationFisherNSW.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:28:39.601474+00:00
-- url     : https://prove2.me/submissions/6a4c0855-1fa4-48d8-811d-3d1e82895cdd

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
import Definitions.Def_SatiationFisherNSW_RoundingRun
open scoped Classical

open SatiationFisherNSW in
theorem solution
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p)
    (R : RoundingRun B G) (hR : R.IsValid I.market x p) :
    (∀ i, ¬ I.market.InB0 p i →
      (R.IsPPRoot I.market x p i → I.market.utility i (x i) / 2 ≤ R.ppUtility I.market x p i) ∧
      (¬ R.IsPPRoot I.market x p i → I.market.utility i (x i) ≤ R.ppUtility I.market x p i)) ∧
    (∀ j, 1 < p j → (∃ i, R.parentGood i = some j) →
      R.keptChild I.market x p j ≠ none) := by
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
  have hx0' : ∀ i j, 0 ≤ x i j := fun i j => (hbuy i).1.1 j
  obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8⟩ := hR
  have hab : ∀ i, ¬ I.market.InB0 p i → I.market.activeBudget p i = min 1 (I.c i) := by
    intro i hi
    unfold FisherMarket.activeBudget
    rw [hN i hi, div_one]
    rfl
  have hab_le : ∀ i, I.market.activeBudget p i ≤ 1 := fun i => min_le_left _ _
  have hsup1 : ∀ j, ∑ i, x i j ≤ 1 := by
    intro j
    refine le_trans (hsup j) ?_
    rw [hes]
    split_ifs
    · exact le_refl 1
    · exact min_le_left _ _
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨hspend, hutil, -⟩ := ha i hi
    obtain ⟨hdem, hthr, hmod⟩ := hbuy i
    have hx0 := hdem.1
    have hTS : ∑ j, I.market.u i j * x i j = ∑ j, p j * x i j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rcases (hx0 j).lt_or_eq with h | h
      · rw [(hmbb_eq i j hi (hthr j h)).1]
      · rw [← h]; simp
    obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = min 1 (I.c i) := ⟨_, rfl⟩
    have hμc : μ ≤ I.c i := by rw [hμ]; exact min_le_right _ _
    have hμ0 : 0 ≤ μ := by rw [hμ]; exact le_min zero_le_one (hcpos i).le
    have htot : ∑ j, I.market.u i j * x i j = μ := by rw [hTS, hspend, hμ]
    have hut : I.market.utility i (x i) = μ := by rw [hutil, hμ]
    have hux0 : ∀ j, 0 ≤ I.market.u i j * x i j := fun j => mul_nonneg (hu0 i j) (hx0 j)
    -- split the sum according to the pp-goods
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => R.parentAgent j = some i ∨ R.keptChild I.market x p j = some i)
      (fun j => I.market.u i j * x i j)
    rw [htot] at hsplit
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ j ∈ Finset.univ.filter
        (fun j => R.parentAgent j = some i ∨ R.keptChild I.market x p j = some i),
        I.market.u i j * x i j := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ j ∈ Finset.univ.filter
        (fun j => ¬ (R.parentAgent j = some i ∨ R.keptChild I.market x p j = some i)),
        I.market.u i j * x i j := ⟨_, rfl⟩
    rw [← hA, ← hC] at hsplit
    have hpp : R.ppUtility I.market x p i = min (I.c i) A := by
      rw [hA]; rfl
    -- bound on the complement
    have hCle : C ≤ ∑ j, (if R.parentGood i = some j ∧ ¬ R.keptChild I.market x p j = some i
        then I.market.u i j * x i j else 0) := by
      rw [hC]
      refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ
        (Finset.univ.filter
          (fun j => ¬ (R.parentAgent j = some i ∨ R.keptChild I.market x p j = some i))))
        (fun j _ _ => by split_ifs <;> first | exact hux0 j | exact le_refl 0))
      apply Finset.sum_le_sum
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      push_neg at hj'
      rcases (hx0 j).lt_or_eq with h | h
      · have h1 := (hv1 i j).mp h
        have hpg : R.parentGood i = some j := by
          rcases h1 with h1 | h1
          · exact absurd h1 hj'.1
          · exact h1
        rw [if_pos ⟨hpg, hj'.2⟩]
      · rw [← h, mul_zero]
        split_ifs <;> simp
    constructor
    · intro hroot
      have hloss : ∑ j, (if R.parentGood i = some j ∧ ¬ R.keptChild I.market x p j = some i
          then I.market.u i j * x i j else 0) ≤ μ / 2 := by
        rcases hpg : R.parentGood i with _ | g0
        · simp
          linarith
        · have hsum1 : ∑ j, (if some g0 = some j ∧ ¬ R.keptChild I.market x p j = some i
              then I.market.u i j * x i j else 0)
              = if ¬ R.keptChild I.market x p g0 = some i then I.market.u i g0 * x i g0 else 0 := by
            rw [Finset.sum_eq_single g0]
            · simp
            · intro j _ hj
              rw [if_neg]
              rintro ⟨h1, -⟩
              exact hj (Option.some_injective _ h1).symm
            · intro h; exact absurd (Finset.mem_univ g0) h
          rw [hsum1]
          by_cases hkc0 : R.keptChild I.market x p g0 = some i
          · rw [if_neg (not_not.mpr hkc0)]; linarith
          · rw [if_pos hkc0]
            have hkc := hkc0
            -- the parent good is cut: its share is at most half
            rcases (hx0 g0).lt_or_eq with hxg | hxg
            · obtain ⟨hug, hpg0⟩ := hmbb_eq i g0 hi (hthr g0 hxg)
              rw [hug]
              have hpne : p g0 ≠ 0 := hpg0.ne'
              have hkc' := hkc
              unfold RoundingRun.keptChild at hkc'
              rcases hlc : R.largestChild g0 with _ | a
              · exact absurd hpg (hv6 g0 hlc i)
              · rw [hlc] at hkc'
                simp only at hkc'
                by_cases hai : a = i
                · subst hai
                  have hnk : ¬ RoundingRun.KeepCond I.market x p a g0 := by
                    intro hk
                    rw [if_pos hk] at hkc'
                    exact hkc' rfl
                  unfold RoundingRun.KeepCond at hnk
                  rw [if_neg hpne, hab a hi, ← hμ] at hnk
                  push_neg at hnk
                  have hx1 : x a g0 ≤ 1 := by
                    refine le_trans ?_ (hsup1 g0)
                    exact Finset.single_le_sum (fun i' _ => hx0' i' g0) (Finset.mem_univ a)
                  nlinarith [hx0 g0]
                · obtain ⟨hpa, hmax⟩ := hv5 g0 a hlc
                  have hxa := hmax i hpg
                  have hpair : x i g0 + x a g0 ≤ ∑ i', x i' g0 := by
                    have := Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.subset_univ ({i, a} : Finset B)) (fun i' _ _ => hx0' i' g0)
                    rw [Finset.sum_pair (Ne.symm hai)] at this
                    exact this
                  have hpe := he g0
                  have hpc : p g0 ≤ I.c i := by rw [← hug]; exact huc i g0
                  have hmin : min (p g0) 1 ≤ μ := by
                    rw [hμ, min_comm]
                    exact min_le_min_left 1 hpc
                  nlinarith [hx0 g0]
            · rw [← hxg, mul_zero]; linarith
      rw [hut, hpp]
      have hA2 : μ / 2 ≤ A := by linarith
      calc μ / 2 ≤ min (I.c i) (μ / 2) := le_min (by linarith) (le_refl _)
        _ ≤ min (I.c i) A := min_le_min_left _ hA2
    · intro hroot
      unfold RoundingRun.IsPPRoot at hroot
      push_neg at hroot
      obtain ⟨g0, hpg, hkg⟩ := hroot
      have hzero : ∑ j, (if R.parentGood i = some j ∧ ¬ R.keptChild I.market x p j = some i
          then I.market.u i j * x i j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rw [hpg] at h1
        rw [← Option.some_injective _ h1] at h2
        exact h2 hkg
      rw [hut, hpp]
      have hA2 : μ ≤ A := by
        have hC0 : 0 ≤ C := by
          rw [hC]; exact Finset.sum_nonneg (fun j _ => hux0 j)
        linarith
      calc μ = min (I.c i) μ := (min_eq_right hμc).symm
        _ ≤ min (I.c i) A := min_le_min_left _ hA2
  · intro j hpj hex
    obtain ⟨i, hi⟩ := hex
    unfold RoundingRun.keptChild
    rcases hlc : R.largestChild j with _ | a
    · exact absurd hi (hv6 j hlc i)
    · simp only
      have hk : RoundingRun.KeepCond I.market x p a j := by
        unfold RoundingRun.KeepCond
        rw [if_neg (by linarith : p j ≠ 0)]
        have := hab_le a
        linarith
      rw [if_pos hk]
      exact Option.some_ne_none a
