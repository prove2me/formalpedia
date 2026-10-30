-- Prove2me | solution 1 for PutermanMDP.Multichain.laurent_improvement
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:27:50.033023+00:00
-- url     : https://prove2.me/submissions/37d8c526-b8d3-4673-a36e-481f0a876f84

import Mathlib
import Definitions.Def_PutermanMDP_Multichain_Criteria

open MarkovDecisionProcesses Filter
open scoped Topology Matrix
open PutermanMDP.Multichain

namespace LauAux

def nxt (s a : Bool) : Bool := if s = false ∧ a = false then false else true

def M0 : StationaryMDP Bool Bool where
  admissible := fun s => if s then {false} else {false, true}
  admissible_nonempty := fun s => by cases s <;> simp
  reward := fun s a => if s = false ∧ a = false then 1 else 0
  trans := fun s a j => if j = nxt s a then 1 else 0
  trans_nonneg := fun s a j => by split_ifs <;> norm_num
  trans_sum := fun s a => by cases s <;> cases a <;> simp [nxt]

def d0 : Rule M0 := ⟨fun _ => false, fun s => by cases s <;> simp [M0]⟩
def e0 : Rule M0 := ⟨fun s => if s then false else true, fun s => by cases s <;> simp [M0]⟩

@[simp] theorem M0_adm (s : Bool) : M0.admissible s = if s then {false} else {false, true} := rfl
@[simp] theorem M0_rew (s a : Bool) : M0.reward s a = if s = false ∧ a = false then 1 else 0 := rfl
@[simp] theorem M0_tr (s a j : Bool) : M0.trans s a j = if j = nxt s a then 1 else 0 := rfl
@[simp] theorem d0_val (s : Bool) : d0.val s = false := rfl
@[simp] theorem e0_val (s : Bool) : e0.val s = if s then false else true := rfl
@[simp] theorem pq (t : ℕ) (h : List (Bool × Bool)) (s a : Bool) :
    (policy M0 d0).q t h s a = if a = false then 1 else 0 := rfl

theorem tr_d (N : ℕ) : ∀ (t : ℕ) (h : List (Bool × Bool)) (s : Bool),
    totalReward (policy M0 d0) N t h s = if s = false then (N : ℝ) else 0 := by
  induction N with
  | zero => intro t h s; simp [totalReward]
  | succ k ih =>
    intro t h s
    cases s
    · simp [totalReward, nxt, ih]
      ring
    · simp [totalReward, nxt, ih]

theorem gain_d : ∀ s, gain M0 d0 s = if s = false then 1 else 0 := by
  intro s
  unfold gain gainInf
  have : (fun N : ℕ => totalReward (policy M0 d0) N 0 [] s / N) =ᶠ[atTop]
      fun _ => if s = false then (1:ℝ) else 0 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [tr_d]
    have : (N:ℝ) ≠ 0 := by positivity
    cases s <;> simp [this]
  rw [Filter.liminf_congr this, Filter.liminf_const]

theorem bias_d : ∀ s, bias M0 d0 s = 0 := by
  intro s
  unfold bias
  have : (fun N : ℕ => (∑ k ∈ Finset.range N,
      (totalReward (policy M0 d0) (k + 1) 0 [] s - ((k + 1 : ℕ) : ℝ) * gain M0 d0 s)) / N) = fun _ => 0 := by
    funext N
    have : ∀ k ∈ Finset.range N, (totalReward (policy M0 d0) (k + 1) 0 [] s - ((k + 1 : ℕ) : ℝ) * gain M0 d0 s) = 0 := by
      intro k _
      rw [tr_d, gain_d]
      cases s <;> simp
    rw [Finset.sum_eq_zero this]; simp
  rw [this, Filter.liminf_const]

theorem rew_d : ∀ n : ℕ, ∀ s, rewardAt M0 d0 n s = if s = false then 1 else 0 := by
  intro n
  induction n with
  | zero => intro s; cases s <;> simp [rewardAt]
  | succ k ih =>
    intro s
    cases s <;> simp [rewardAt, act, nxt, ih]

theorem disc_d (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    discounted M0 d0 lam false = 1 / (1 - lam) ∧ discounted M0 d0 lam true = 0 := by
  constructor
  · unfold discounted
    simp only [rew_d]
    simp
    rw [tsum_geometric_of_lt_one h0 h1]
  · unfold discounted
    simp only [rew_d]
    simp

theorem resid_e (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    PutermanMDP.Multichain.residual M0 e0 d0 lam false = 1 := by
  have hl : (1 - lam) ≠ 0 := by linarith
  have := disc_d lam h0 h1
  unfold PutermanMDP.Multichain.residual advantage
  simp [act, nxt, this.1, this.2, gain_d, bias_d]
  field_simp
  ring

end LauAux

theorem solution : ¬ (∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty S]
    [DecidableEq S] (M : StationaryMDP S A) (δ d : Rule M),
    (∀ lam : ℝ, 0 ≤ lam → lam < 1 →
      (1 - lam • Matrix.of (transMatrix M δ.val))⁻¹ *ᵥ advantage M δ d lam =
        discounted M δ lam - discounted M d lam) ∧
    (∀ (lam : ℝ) (s : S), 0 ≤ lam → lam < 1 → δ.val s = d.val s →
      advantage M δ d lam s = 0) ∧
    Filter.Tendsto (PutermanMDP.Multichain.residual M δ d) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) := by
  intro H
  have h3 := (H LauAux.M0 LauAux.e0 LauAux.d0).2.2
  have h4 : Tendsto (fun lam => PutermanMDP.Multichain.residual LauAux.M0 LauAux.e0 LauAux.d0 lam false)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
    ((continuous_apply false).tendsto _).comp h3
  have h5 : (fun lam => PutermanMDP.Multichain.residual LauAux.M0 LauAux.e0 LauAux.d0 lam false) =ᶠ[nhdsWithin (1 : ℝ) (Set.Iio 1)]
      fun _ => (1:ℝ) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with lam hl
    exact LauAux.resid_e lam hl.1.le hl.2
  have h6 := h4.congr' h5
  have := tendsto_nhds_unique h6 tendsto_const_nhds
  norm_num at this
