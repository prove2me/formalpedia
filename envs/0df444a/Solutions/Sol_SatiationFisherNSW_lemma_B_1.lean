-- Prove2me | solution 1 for SatiationFisherNSW.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:27:09.616892+00:00
-- url     : https://prove2.me/submissions/ea2a56d3-24f0-4b38-b7c1-8a3dd1ffdffb

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
    ∀ i, I.market.InB0 p i →
      (R.IsPPRoot I.market x p i → I.c i / 2 ≤ R.ppUtility I.market x p i) ∧
      (¬ R.IsPPRoot I.market x p i → I.c i ≤ R.ppUtility I.market x p i) := by
  intro i hB0
  obtain ⟨j0, hp0, hu0⟩ := hB0
  have hcc : I.market.c i = I.c i := rfl
  have hcpos : 0 < I.c i := I.c_pos i
  have hunn : ∀ k, 0 ≤ I.market.u i k := fun k => I.market.u_nonneg i k
  have hxnn : ∀ a k, 0 ≤ x a k := fun a k => (hEq.2.2.1 a).1.1 k
  have hgnn : ∀ k, 0 ≤ I.market.u i k * x i k := fun k => mul_nonneg (hunn k) (hxnn i k)
  -- total utility is at least c
  have htot : I.c i ≤ ∑ k, I.market.u i k * x i k := by
    have hdem := (hEq.2.2.1 i).1
    obtain ⟨t, ht⟩ : ∃ t, t = I.c i / I.market.u i j0 := ⟨_, rfl⟩
    have htnn : 0 ≤ t := by rw [ht]; exact div_nonneg hcpos.le (hunn j0)
    obtain ⟨z, hz⟩ : ∃ z : G → ℝ, z = fun k => x i k + if k = j0 then t else 0 := ⟨_, rfl⟩
    have hzk : ∀ k, z k = x i k + if k = j0 then t else 0 := fun k => by rw [hz]
    have hz0 : ∀ k, 0 ≤ z k := by
      intro k
      rw [hzk]
      split_ifs
      · linarith [hxnn i k]
      · linarith [hxnn i k]
    have e2 : ∀ k, p k * z k = p k * x i k + (if k = j0 then p k * t else 0) := by
      intro k
      rw [hzk]
      split_ifs <;> ring
    have hzp : ∑ k, p k * z k = ∑ k, p k * x i k := by
      rw [Finset.sum_congr rfl (fun k _ => e2 k), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), hp0, zero_mul, add_zero]
    have e1 : ∀ k, I.market.u i k * z k =
        I.market.u i k * x i k + (if k = j0 then I.market.u i k * t else 0) := by
      intro k
      rw [hzk]
      split_ifs <;> ring
    have hut1 : I.market.u i j0 * t = I.c i := by
      rw [ht]; exact mul_div_cancel₀ _ (ne_of_gt hu0)
    have hzu : ∑ k, I.market.u i k * z k = ∑ k, I.market.u i k * x i k + I.c i := by
      rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), hut1]
    have hbud : ∑ k, p k * z k ≤ I.market.m i := by rw [hzp]; exact hdem.2.1
    have hut := hdem.2.2 z hz0 hbud
    unfold FisherMarket.utility at hut
    rw [hzu, hcc] at hut
    have hS : 0 ≤ ∑ k, I.market.u i k * x i k := Finset.sum_nonneg (fun k _ => hgnn k)
    rw [min_eq_left (show I.c i ≤ ∑ k, I.market.u i k * x i k + I.c i by linarith)] at hut
    exact le_trans hut (min_le_right _ _)
  -- the set of goods kept by i in the pp-graph
  have hkey : ∀ k, ¬ (R.parentAgent k = some i ∨ R.keptChild I.market x p k = some i) →
      R.parentGood i ≠ some k → I.market.u i k * x i k = 0 := by
    intro k hk hpg
    by_contra hne
    have hx0 : x i k ≠ 0 := by
      intro h0; apply hne; rw [h0, mul_zero]
    have hxpos : 0 < x i k := lt_of_le_of_ne (hxnn i k) (Ne.symm hx0)
    rcases (hR.1 i k).mp hxpos with h | h
    · exact hk (Or.inl h)
    · exact hpg h
  have hsplit : ∑ k ∈ Finset.univ.filter
        (fun k => R.parentAgent k = some i ∨ R.keptChild I.market x p k = some i),
        I.market.u i k * x i k + ∑ k ∈ Finset.univ.filter
        (fun k => ¬ (R.parentAgent k = some i ∨ R.keptChild I.market x p k = some i)),
        I.market.u i k * x i k = ∑ k, I.market.u i k * x i k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hpp : R.ppUtility I.market x p i = min (I.c i)
      (∑ k ∈ Finset.univ.filter
        (fun k => R.parentAgent k = some i ∨ R.keptChild I.market x p k = some i),
        I.market.u i k * x i k) := rfl
  by_cases hJ : ∃ j, R.parentGood i = some j ∧
      ¬ (R.parentAgent j = some i ∨ R.keptChild I.market x p j = some i)
  · obtain ⟨js, hpg, hjF⟩ := hJ
    -- the dropped parent good contributes at most c/2
    have hxpos : 0 < x i js := (hR.1 i js).mpr (Or.inr hpg)
    have hmbb := (hEq.2.2.1 i).2.1 js hxpos
    have hineq := hmbb.2 j0
    rw [hp0, mul_zero] at hineq
    have hpj : p js = 0 := by
      by_contra hne
      have hpos : 0 < p js := lt_of_le_of_ne (hEq.1 js) (Ne.symm hne)
      have : 0 < I.market.u i j0 * p js := mul_pos hu0 hpos
      linarith
    have hsup := hEq.2.1 js
    have hms : I.market.modestSupply p js = 1 := by
      unfold FisherMarket.modestSupply
      rw [if_pos hpj]
    rw [hms] at hsup
    have hule : I.market.u i js ≤ I.c i := min_le_right _ _
    have hgj : I.market.u i js * x i js ≤ I.c i / 2 := by
      cases hlc : R.largestChild js with
      | none => exact absurd hpg (hR.2.2.2.2.2.1 js hlc i)
      | some i0 =>
        have hlc' := hR.2.2.2.2.1 js i0 hlc
        have hkc : R.keptChild I.market x p js =
            if RoundingRun.KeepCond I.market x p i0 js then some i0 else none := by
          simp only [RoundingRun.keptChild, hlc]
        by_cases hi : i0 = i
        · rw [hi] at hkc
          have hnK : ¬ RoundingRun.KeepCond I.market x p i js := by
            intro hK
            rw [if_pos hK] at hkc
            exact hjF (Or.inr hkc)
          unfold RoundingRun.KeepCond at hnK
          rw [if_pos hpj] at hnK
          push_neg at hnK
          exact hnK
        · have hle := hlc'.2 i hpg
          have hpair : x i js + x i0 js ≤ ∑ k, x k js := by
            have h1 : ∑ k ∈ ({i, i0} : Finset B), x k js = x i js + x i0 js :=
              Finset.sum_pair (Ne.symm hi)
            rw [← h1]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun k _ _ => hxnn k js)
          have hxh : x i js ≤ 1 / 2 := by linarith
          have hun := hunn js
          nlinarith [mul_le_mul hule hxh (hxnn i js) hcpos.le]
    have hnotF : ∑ k ∈ Finset.univ.filter
        (fun k => ¬ (R.parentAgent k = some i ∨ R.keptChild I.market x p k = some i)),
        I.market.u i k * x i k = I.market.u i js * x i js := by
      apply Finset.sum_eq_single_of_mem js
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hjF⟩
      · intro b hb hbj
        rw [Finset.mem_filter] at hb
        apply hkey b hb.2
        intro h
        rw [hpg] at h
        exact hbj (Option.some.inj h).symm
    refine ⟨fun _ => ?_, fun hroot => ?_⟩
    · rw [hpp]
      refine le_min ?_ ?_
      · linarith
      · linarith
    · exfalso
      apply hroot
      unfold RoundingRun.IsPPRoot
      intro j hj hkc
      rw [hpg] at hj
      have hjj : js = j := Option.some.inj hj
      subst hjj
      exact hjF (Or.inr hkc)
  · push_neg at hJ
    have hnotF : ∑ k ∈ Finset.univ.filter
        (fun k => ¬ (R.parentAgent k = some i ∨ R.keptChild I.market x p k = some i)),
        I.market.u i k * x i k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_filter] at hk
      apply hkey k hk.2
      intro h
      exact hk.2 (hJ k h)
    have hge : I.c i ≤ ∑ k ∈ Finset.univ.filter
        (fun k => R.parentAgent k = some i ∨ R.keptChild I.market x p k = some i),
        I.market.u i k * x i k := by linarith
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [hpp]
      exact le_min (by linarith) (by linarith)
    · rw [hpp]
      exact le_min le_rfl hge
