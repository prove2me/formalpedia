-- Prove2me | solution 1 for SatiationFisherNSW.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:32:50.339114+00:00
-- url     : https://prove2.me/submissions/367ff2ad-058b-4076-b894-aea8fd3f3e08

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
    ∀ i j, ¬ I.market.InB0 p i → R.keptChild I.market x p j = some i →
      R.output I.market x p j = some i →
        I.market.utility i (x i) / 2 ≤ I.val i (R.output I.market x p) := by
  intro i j hnB0 hk hout
  have hcc : I.market.c i = I.c i := rfl
  have hm : I.market.m i = 1 := rfl
  have hcpos : 0 < I.c i := I.c_pos i
  have hunn : ∀ k, 0 ≤ I.market.u i k := fun k => I.market.u_nonneg i k
  have hxnn : ∀ k, 0 ≤ x i k := fun k => (hEq.2.2.1 i).1.1 k
  have hpnn : ∀ k, 0 ≤ p k := hEq.1
  have hrat1 : I.market.mbbRatio p i = 1 := hN i hnB0
  -- MBB goods with positive price have u = p
  have hratio : ∀ k, I.market.IsMBB p i k → 0 < p k → I.market.u i k = p k := by
    intro k hmbb hpk
    haveI : Nonempty G := ⟨k⟩
    have hsup : I.market.mbbRatio p i = I.market.u i k / p k := by
      unfold FisherMarket.mbbRatio
      apply le_antisymm
      · refine ciSup_le (fun k' => ?_)
        by_cases hk' : p k' = 0
        · rw [hk', div_zero]
          exact div_nonneg (hunn k) hpk.le
        · have hpos : 0 < p k' := lt_of_le_of_ne (hpnn k') (Ne.symm hk')
          rw [div_le_div_iff₀ hpos hpk]
          exact hmbb.2 k'
      · exact le_ciSup (Set.finite_range (fun k' : G => I.market.u i k' / p k')).bddAbove k
    rw [hrat1] at hsup
    exact ((div_eq_one_iff_eq hpk.ne').mp hsup.symm)
  -- goods bought have positive price
  have hpos_of_mbb : ∀ k, I.market.IsMBB p i k → 0 < p k := by
    intro k hmbb
    by_contra hle
    have hp0 : p k = 0 := le_antisymm (not_lt.mp hle) (hpnn k)
    exact hnB0 ⟨k, hp0, hmbb.1⟩
  -- utility bound
  have hux : ∑ k, I.market.u i k * x i k = ∑ k, p k * x i k := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hx0 : x i k = 0
    · rw [hx0, mul_zero, mul_zero]
    · have hxpos : 0 < x i k := lt_of_le_of_ne (hxnn k) (Ne.symm hx0)
      have hmbb := (hEq.2.2.1 i).2.1 k hxpos
      rw [hratio k hmbb (hpos_of_mbb k hmbb)]
  have hbud : ∑ k, p k * x i k ≤ 1 := by rw [← hm]; exact (hEq.2.2.1 i).1.2.1
  have hutil_le : I.market.utility i (x i) ≤ min 1 (I.c i) := by
    unfold FisherMarket.utility
    rw [hcc]
    apply le_min
    · exact le_trans (min_le_right _ _) (by rw [hux]; exact hbud)
    · exact min_le_left _ _
  -- the kept good
  have hlc : R.largestChild j = some i ∧ RoundingRun.KeepCond I.market x p i j := by
    unfold RoundingRun.keptChild at hk
    split at hk
    · exact absurd hk (by simp)
    · rename_i i' h
      by_cases hK : RoundingRun.KeepCond I.market x p i' j
      · rw [if_pos hK] at hk
        have hii : i' = i := Option.some.inj hk
        rw [hii] at h hK
        exact ⟨h, hK⟩
      · rw [if_neg hK] at hk
        exact absurd hk (by simp)
  obtain ⟨hlcj, hK⟩ := hlc
  have hpg : R.parentGood i = some j := (hR.2.2.2.2.1 j i hlcj).1
  have hxpos : 0 < x i j := (hR.1 i j).mpr (Or.inr hpg)
  have hmbbj := (hEq.2.2.1 i).2.1 j hxpos
  have hpj := hpos_of_mbb j hmbbj
  have huj : I.market.u i j = p j := hratio j hmbbj hpj
  unfold RoundingRun.KeepCond at hK
  rw [if_neg (ne_of_gt hpj)] at hK
  have hab : I.market.activeBudget p i = min 1 (I.c i) := by
    unfold FisherMarket.activeBudget
    rw [hrat1, hm, hcc, div_one]
  rw [hab] at hK
  -- valuation
  have hu : I.market.u i j = min (I.v i j) (I.c i) := rfl
  unfold NSWInstance.val
  have hmem : j ∈ Finset.univ.filter (fun j' => R.output I.market x p j' = some i) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hout⟩
  have hsum : I.v i j ≤ ∑ j' ∈ Finset.univ.filter (fun j' => R.output I.market x p j' = some i),
      I.v i j' :=
    Finset.single_le_sum (f := fun j' => I.v i j') (fun k _ => I.v_nonneg i k) hmem
  have hval : I.market.u i j ≤ min (I.c i)
      (∑ j' ∈ Finset.univ.filter (fun j' => R.output I.market x p j' = some i), I.v i j') := by
    rw [hu]
    exact le_min (min_le_right _ _) (le_trans (min_le_left _ _) hsum)
  linarith
