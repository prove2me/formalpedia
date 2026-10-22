-- Prove2me | solution 1 for RubinsteinNash.WeakNash.claim_8_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:56:44.545004+00:00
-- url     : https://prove2.me/submissions/d292f2ba-77a8-4e4a-881b-3715cf004beb

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria
set_option autoImplicit false
open Finset

theorem ll_pp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (x : ∀ i, S i → ℝ) (p : ι) (y : S p → ℝ) (s : ∀ i, S i) :
    AGT.profileProb (Function.update x p y) s = y (s p) * ∏ i ∈ univ.erase p, x i (s i) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ p)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem ll_lin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) (y : S p → ℝ) :
    AGT.expectedPayoff u (Function.update x p y) p
      = ∑ j : S p, y j * DGPNash.NashMap.purePayoff u x p j := by
  simp only [AGT.expectedPayoff, DGPNash.NashMap.purePayoff, ll_pp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_eq_single (s p)]
  · simp [mul_assoc]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem ll_key {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x)
    (ε k : ℝ) (hε : 0 < ε) (hk : 1 < k) (v : ι)
    (hv : RubinsteinNash.WeakNash.IsEpsBestResponse u x ε v) :
    ε * k * DGPNash.WellSupported.trimMass u x ε k v ≤ ε := by
  obtain ⟨hx0, hx1⟩ := hx v
  set U : S v → ℝ := fun j => DGPNash.NashMap.purePayoff u x v j with hUdef
  set E := AGT.expectedPayoff u x v with hEdef
  have hU : ∀ j, U j - ε ≤ E := fun j =>
    hv (fun k => if k = j then 1 else 0)
      ⟨fun a => by dsimp only; split_ifs <;> norm_num, by simp⟩
  have hE : E = ∑ j, x v j * U j := by
    have := ll_lin u x v (x v)
    rw [Function.update_eq_self] at this
    exact this
  have : Nonempty (S v) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hx1
  have hMle : DGPNash.WellSupported.maxPurePayoff u x v ≤ E + ε := by
    apply ciSup_le
    intro j; linarith [hU j]
  have hUM : ∀ j, U j ≤ DGPNash.WellSupported.maxPurePayoff u x v := fun j =>
    le_ciSup (Set.finite_range _).bddAbove j
  set Mx := DGPNash.WellSupported.maxPurePayoff u x v with hM
  have hsum : ∑ j, x v j * (Mx - U j) ≤ ε := by
    have : ∑ j, x v j * (Mx - U j) = Mx - E := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hx1, one_mul, ← hE]
    linarith
  have hz : ε * k * DGPNash.WellSupported.trimMass u x ε k v ≤ ∑ j, x v j * (Mx - U j) := by
    unfold DGPNash.WellSupported.trimMass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases h : DGPNash.NashMap.purePayoff u x v j < Mx - ε * k
    · rw [if_pos h]
      have h' : U j < Mx - ε * k := h
      have : ε * k ≤ Mx - U j := by linarith
      nlinarith [hx0 j]
    · rw [if_neg h]
      simp only [mul_zero]
      exact mul_nonneg (hx0 j) (by linarith [hUM j])
  linarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x)
    (ε k : ℝ) (hε : 0 < ε) (hk : 1 < k) :
    ∀ v : ι, ∑ s : S v, |RubinsteinNash.WeakNash.weakTrim u x ε k v s - x v s| ≤ 2 / (k - 1) := by
  intro v
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have h2 : 0 ≤ 2 / (k - 1) := by positivity
  by_cases hb : RubinsteinNash.WeakNash.IsEpsBestResponse u x ε v
  · have hz := ll_key u x hx ε k hε hk v hb
    set z := DGPNash.WellSupported.trimMass u x ε k v with hzdef
    have hzk : z ≤ 1 / k := by
      rw [le_div_iff₀ hk0]
      have : ε * (z * k) ≤ ε * 1 := by nlinarith
      exact le_of_mul_le_mul_left this hε
    have hz1 : z < 1 := lt_of_le_of_lt hzk (by rw [div_lt_one hk0]; exact hk)
    have hz1' : 0 < 1 - z := by linarith
    obtain ⟨hx0, hx1⟩ := hx v
    set Mx := DGPNash.WellSupported.maxPurePayoff u x v with hM
    set g : S v → ℝ := fun s =>
      if DGPNash.NashMap.purePayoff u x v s < Mx - ε * k then x v s else 0 with hg
    have hgz : ∑ s, g s = z := rfl
    have hz0 : 0 ≤ z := Finset.sum_nonneg (fun j _ => by
      split_ifs
      exacts [hx0 j, le_refl 0])
    have hterm : ∀ s, |RubinsteinNash.WeakNash.weakTrim u x ε k v s - x v s|
        = g s + (x v s - g s) * (z / (1 - z)) := by
      intro s
      simp only [RubinsteinNash.WeakNash.weakTrim, if_pos hb, DGPNash.WellSupported.trim, ← hzdef, ← hM]
      by_cases h : DGPNash.NashMap.purePayoff u x v s < Mx - ε * k
      · have hn : ¬ (DGPNash.NashMap.purePayoff u x v s ≥ Mx - ε * k) := not_le.mpr h
        simp only [hg, if_pos h, if_neg hn]
        simp [abs_of_nonneg (hx0 s)]
      · have hp : DGPNash.NashMap.purePayoff u x v s ≥ Mx - ε * k := not_lt.mp h
        simp only [hg, if_neg h, if_pos hp]
        have : x v s / (1 - z) - x v s = x v s * (z / (1 - z)) := by
          field_simp; ring
        rw [this, abs_of_nonneg (mul_nonneg (hx0 s) (div_nonneg hz0 hz1'.le))]
        ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hx1, hgz]
    have : z + (1 - z) * (z / (1 - z)) = 2 * z := by field_simp; ring
    rw [this]
    calc 2 * z ≤ 2 * (1 / k) := by linarith
      _ ≤ 2 / (k - 1) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left (by norm_num) hk1 (by linarith)
  · have : ∀ s, RubinsteinNash.WeakNash.weakTrim u x ε k v s - x v s = 0 := by
      intro s
      simp [RubinsteinNash.WeakNash.weakTrim, hb]
    simp_rw [this]
    simpa using h2
