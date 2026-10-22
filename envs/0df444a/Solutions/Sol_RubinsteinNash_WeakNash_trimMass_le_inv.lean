-- Prove2me | solution 1 for RubinsteinNash.WeakNash.trimMass_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:56:15.788398+00:00
-- url     : https://prove2.me/submissions/3b7068fa-6465-4035-bd2e-425380569a9a

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
    (ε k : ℝ) (hε : 0 < ε) (hk : 1 < k) (v : ι) (hv : RubinsteinNash.WeakNash.IsEpsBestResponse u x ε v) :
    DGPNash.WellSupported.trimMass u x ε k v ≤ 1 / k := by
  have h := ll_key u x hx ε k hε hk v hv
  have hk0 : 0 < k := by linarith
  rw [le_div_iff₀ hk0]
  have : ε * (DGPNash.WellSupported.trimMass u x ε k v * k) ≤ ε * 1 := by nlinarith
  exact le_of_mul_le_mul_left this hε
