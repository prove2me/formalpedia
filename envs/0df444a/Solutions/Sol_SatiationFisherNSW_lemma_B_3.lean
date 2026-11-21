-- Prove2me | solution 1 for SatiationFisherNSW.lemma_B_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:21:18.85099+00:00
-- url     : https://prove2.me/submissions/4098b490-494a-4125-b994-53e4081523be

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
    ∀ i j, I.market.InB0 p i → R.keptChild I.market x p j = some i →
      R.output I.market x p j = some i → I.c i / 2 ≤ I.val i (R.output I.market x p) := by
  intro i j hB0 hk hout
  -- extract largest child and keep condition
  have hlc : R.largestChild j = some i ∧ RoundingRun.KeepCond I.market x p i j := by
    unfold RoundingRun.keptChild at hk
    split at hk
    · exact absurd hk (by simp)
    · rename_i i' h
      by_cases hK : RoundingRun.KeepCond I.market x p i' j
      · rw [if_pos hK] at hk
        have hii : i' = i := Option.some.inj hk
        subst hii
        exact ⟨h, hK⟩
      · rw [if_neg hK] at hk
        exact absurd hk (by simp)
  obtain ⟨hlcj, hK⟩ := hlc
  have hpg : R.parentGood i = some j := (hR.2.2.2.2.1 j i hlcj).1
  have hxpos : 0 < x i j := (hR.1 i j).mpr (Or.inr hpg)
  -- p j = 0 via thrifty + InB0
  obtain ⟨j0, hp0, hu0⟩ := hB0
  have hmbb := (hEq.2.2.1 i).2.1 j hxpos
  have hineq := hmbb.2 j0
  rw [hp0, mul_zero] at hineq
  have hpj0 : 0 ≤ p j := hEq.1 j
  have hpj : p j = 0 := by
    by_contra hne
    have hpos : 0 < p j := lt_of_le_of_ne hpj0 (Ne.symm hne)
    have : 0 < I.market.u i j0 * p j := mul_pos hu0 hpos
    linarith
  unfold RoundingRun.KeepCond at hK
  rw [if_pos hpj] at hK
  -- x i j ≤ 1
  have hsup := hEq.2.1 j
  have hms : I.market.modestSupply p j = 1 := by
    unfold FisherMarket.modestSupply
    rw [if_pos hpj]
  rw [hms] at hsup
  have hxnn : ∀ k, 0 ≤ x k j := fun k => (hEq.2.2.1 k).1.1 j
  have hxle : x i j ≤ 1 := by
    have h1 : x i j ≤ ∑ k, x k j :=
      Finset.single_le_sum (f := fun k => x k j) (fun k _ => hxnn k) (Finset.mem_univ i)
    linarith
  have hu : I.market.u i j = min (I.v i j) (I.c i) := rfl
  have hc : I.market.c i = I.c i := rfl
  rw [hu, min_eq_left (hvc i j), hc] at hK
  have hv0 : 0 ≤ I.v i j := I.v_nonneg i j
  have hvbig : I.c i / 2 < I.v i j := by
    nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hxle)]
  -- valuation
  unfold NSWInstance.val
  have hmem : j ∈ Finset.univ.filter (fun j' => R.output I.market x p j' = some i) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hout⟩
  have hsum : I.v i j ≤ ∑ j' ∈ Finset.univ.filter (fun j' => R.output I.market x p j' = some i),
      I.v i j' :=
    Finset.single_le_sum (f := fun j' => I.v i j') (fun k _ => I.v_nonneg i k) hmem
  have hcpos := I.c_pos i
  exact le_min (by linarith) (by linarith)
