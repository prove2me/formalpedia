-- Prove2me | solution 1 for PutermanMDP.Multichain.policy_iteration_terminates
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:30:18.393986+00:00
-- url     : https://prove2.me/submissions/2ddcb294-d42d-48c0-beff-bcecac3aedd5

import Mathlib
import Definitions.Def_PutermanMDP_Multichain_Iteration

open MarkovDecisionProcesses Filter
open scoped Topology
open PutermanMDP.Multichain

namespace PitAux

def nxt (s : Fin 3) (a : Bool) : Fin 3 := if s = 0 then (if a then 1 else 2) else s

def M0 : StationaryMDP (Fin 3) Bool where
  admissible := fun s => if s = 0 then {true, false} else {false}
  admissible_nonempty := fun s => by by_cases h : s = 0 <;> simp [h]
  reward := fun s a => if s = 0 then (if a then -1 else 0) else if s = 1 then 1 else 0
  trans := fun s a j => if j = nxt s a then 1 else 0
  trans_nonneg := fun s a j => by split_ifs <;> norm_num
  trans_sum := fun s a => by simp

def dx : Rule M0 := ⟨fun s => if s = 0 then true else false, fun s => by by_cases h : s = 0 <;> simp [M0, h]⟩
def dy : Rule M0 := ⟨fun _ => false, fun s => by by_cases h : s = 0 <;> simp [M0, h]⟩

@[simp] theorem M0_adm (s : Fin 3) : M0.admissible s = if s = 0 then {true, false} else {false} := rfl
@[simp] theorem M0_rew (s : Fin 3) (a : Bool) :
    M0.reward s a = if s = 0 then (if a then -1 else 0) else if s = 1 then 1 else 0 := rfl
@[simp] theorem M0_tr (s : Fin 3) (a : Bool) (j : Fin 3) :
    M0.trans s a j = if j = nxt s a then 1 else 0 := rfl
@[simp] theorem dx_val (s : Fin 3) : dx.val s = if s = 0 then true else false := rfl
@[simp] theorem dy_val (s : Fin 3) : dy.val s = false := rfl
@[simp] theorem pqx (t : ℕ) (h : List (Fin 3 × Bool)) (s : Fin 3) (a : Bool) :
    (policy M0 dx).q t h s a = if a = (if s = 0 then true else false) then 1 else 0 := rfl
@[simp] theorem pqy (t : ℕ) (h : List (Fin 3 × Bool)) (s : Fin 3) (a : Bool) :
    (policy M0 dy).q t h s a = if a = false then 1 else 0 := rfl

theorem tr_x (N : ℕ) : ∀ (t : ℕ) (h : List (Fin 3 × Bool)) (s : Fin 3),
    totalReward (policy M0 dx) N t h s =
      if s = 0 then (if N = 0 then 0 else (N:ℝ) - 2) else if s = 1 then (N:ℝ) else 0 := by
  induction N with
  | zero => intro t h s; simp [totalReward]
  | succ k ih =>
    intro t h s
    match s with
    | 0 => simp [totalReward, nxt, ih, Fin.sum_univ_three] <;> ring
    | 1 => simp [totalReward, nxt, ih, Fin.sum_univ_three] <;> ring
    | 2 => simp [totalReward, nxt, ih, Fin.sum_univ_three]

theorem tr_y (N : ℕ) : ∀ (t : ℕ) (h : List (Fin 3 × Bool)) (s : Fin 3),
    totalReward (policy M0 dy) N t h s = if s = 1 then (N:ℝ) else 0 := by
  induction N with
  | zero => intro t h s; simp [totalReward]
  | succ k ih =>
    intro t h s
    match s with
    | 0 => simp [totalReward, nxt, ih, Fin.sum_univ_three]
    | 1 => simp [totalReward, nxt, ih, Fin.sum_univ_three] <;> ring
    | 2 => simp [totalReward, nxt, ih, Fin.sum_univ_three]

theorem gain_x (s : Fin 3) : gainInf (policy M0 dx) s = if s = 2 then 0 else 1 := by
  unfold gainInf
  match s with
  | 0 =>
    have ht : Tendsto (fun N : ℕ => totalReward (policy M0 dx) N 0 [] 0 / N) atTop (𝓝 1) := by
      have h1 : Tendsto (fun N : ℕ => (1:ℝ) - 2 * (1 / (N:ℝ))) atTop (𝓝 1) := by
        have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
        simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have : (N:ℝ) ≠ 0 := by positivity
      rw [tr_x]; simp [hN.ne']; field_simp
    simpa using ht.liminf_eq
  | 1 =>
    have : (fun N : ℕ => totalReward (policy M0 dx) N 0 [] 1 / N) =ᶠ[atTop] fun _ => (1:ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have : (N:ℝ) ≠ 0 := by positivity
      rw [tr_x]; simp [this]
    rw [Filter.liminf_congr this, Filter.liminf_const]; simp
  | 2 =>
    have : (fun N : ℕ => totalReward (policy M0 dx) N 0 [] 2 / N) = fun _ => (0:ℝ) := by
      funext N; rw [tr_x]; simp
    rw [this, Filter.liminf_const]; simp

theorem gain_y (s : Fin 3) : gainInf (policy M0 dy) s = if s = 1 then 1 else 0 := by
  unfold gainInf
  have : (fun N : ℕ => totalReward (policy M0 dy) N 0 [] s / N) =ᶠ[atTop]
      fun _ => if s = 1 then (1:ℝ) else 0 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N:ℝ) ≠ 0 := by positivity
    rw [tr_y]; by_cases h : s = 1 <;> simp [h, this]
  rw [Filter.liminf_congr this, Filter.liminf_const]

theorem bias_x (s : Fin 3) : bias M0 dx s = if s = 0 then -2 else 0 := by
  unfold bias
  have hg : gain M0 dx s = if s = 2 then 0 else 1 := gain_x s
  have : (fun N : ℕ => (∑ k ∈ Finset.range N,
      (totalReward (policy M0 dx) (k + 1) 0 [] s - ((k + 1 : ℕ) : ℝ) * gain M0 dx s)) / N)
      =ᶠ[atTop] fun _ => if s = 0 then (-2:ℝ) else 0 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N:ℝ) ≠ 0 := by positivity
    have : ∀ k ∈ Finset.range N, (totalReward (policy M0 dx) (k + 1) 0 [] s
        - ((k + 1 : ℕ) : ℝ) * gain M0 dx s) = if s = 0 then (-2:ℝ) else 0 := by
      intro k _
      rw [tr_x, hg]
      match s with
      | 0 => simp
      | 1 => simp
      | 2 => simp
    rw [Finset.sum_congr rfl this]
    by_cases h : s = 0 <;> simp [h]
    field_simp
  rw [Filter.liminf_congr this, Filter.liminf_const]

theorem bias_y (s : Fin 3) : bias M0 dy s = 0 := by
  unfold bias
  have hg : gain M0 dy s = if s = 1 then 1 else 0 := gain_y s
  have : (fun N : ℕ => (∑ k ∈ Finset.range N,
      (totalReward (policy M0 dy) (k + 1) 0 [] s - ((k + 1 : ℕ) : ℝ) * gain M0 dy s)) / N)
      = fun _ => 0 := by
    funext N
    have : ∀ k ∈ Finset.range N, (totalReward (policy M0 dy) (k + 1) 0 [] s
        - ((k + 1 : ℕ) : ℝ) * gain M0 dy s) = 0 := by
      intro k _
      rw [tr_y, hg]
      by_cases h : s = 1 <;> simp [h]
    rw [Finset.sum_eq_zero this]; simp
  rw [this, Filter.liminf_const]

def gx : Fin 3 → ℝ := fun s => if s = 2 then 0 else 1
def hx : Fin 3 → ℝ := fun s => if s = 0 then -2 else 0
def gy : Fin 3 → ℝ := fun s => if s = 1 then 1 else 0
def hy : Fin 3 → ℝ := fun _ => 0

theorem gx_eq : gain M0 dx = gx := funext gain_x
theorem gy_eq : gain M0 dy = gy := funext gain_y
theorem hx_eq : bias M0 dx = hx := funext bias_x
theorem hy_eq : bias M0 dy = hy := funext bias_y

theorem eval_x : Evaluation M0 dx gx hx := by
  constructor
  · intro s; match s with
    | 0 => simp [act, nxt, gx, Fin.sum_univ_three]
    | 1 => simp [act, nxt, gx, Fin.sum_univ_three]
    | 2 => simp [act, nxt, gx, Fin.sum_univ_three]
  · intro s; match s with
    | 0 => simp [act, nxt, gx, hx, Fin.sum_univ_three]; norm_num
    | 1 => simp [act, nxt, gx, hx, Fin.sum_univ_three]
    | 2 => simp [act, nxt, gx, hx, Fin.sum_univ_three]

theorem eval_y : Evaluation M0 dy gy hy := by
  constructor
  · intro s; match s with
    | 0 => simp [act, nxt, gy, Fin.sum_univ_three]
    | 1 => simp [act, nxt, gy, Fin.sum_univ_three]
    | 2 => simp [act, nxt, gy, Fin.sum_univ_three]
  · intro s; match s with
    | 0 => simp [act, nxt, gy, hy, Fin.sum_univ_three]
    | 1 => simp [act, nxt, gy, hy, Fin.sum_univ_three]
    | 2 => simp [act, nxt, gy, hy, Fin.sum_univ_three]

theorem step_xy : PrintedStep M0 gx hx dx dy := by
  right
  refine ⟨?_, ?_, ?_⟩
  · intro s a ha
    fin_cases s <;> cases a <;> simp_all [act, nxt, gx, Fin.sum_univ_three]
  · intro s a ha
    fin_cases s <;> cases a <;> simp_all [act, nxt, hx, Fin.sum_univ_three]
  · intro s hs
    fin_cases s
    · exfalso
      have h2 := hs false (by simp)
      simp [act, nxt, hx, Fin.sum_univ_three] at h2
      norm_num at h2
    · simp
    · simp

theorem step_yx : PrintedStep M0 gy hy dy dx := by
  left
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := h 0 true (by simp)
    simp [act, nxt, gy, Fin.sum_univ_three] at this
    norm_num at this
  · intro s a ha
    fin_cases s <;> cases a <;> simp_all [act, nxt, gy, Fin.sum_univ_three]
  · intro s hs
    fin_cases s
    · exfalso
      have := hs true (by simp)
      simp [act, nxt, gy, Fin.sum_univ_three] at this
      norm_num at this
    · simp
    · simp

def dd (n : ℕ) : Rule M0 := if n % 2 = 0 then dy else dx
def gg (n : ℕ) : Fin 3 → ℝ := if n % 2 = 0 then gy else gx
def hh (n : ℕ) : Fin 3 → ℝ := if n % 2 = 0 then hy else hx

theorem run : PrintedRun M0 dd gg hh := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have h1 : (n + 1) % 2 = 1 := by omega
    simp only [dd, gg, hh, hn, h1, if_true]
    simp
    exact ⟨eval_y, hy_eq.symm, step_yx⟩
  · have h1 : (n + 1) % 2 = 0 := by omega
    simp only [dd, gg, hh, hn, h1]
    simp
    exact ⟨eval_x, hx_eq.symm, step_xy⟩

theorem ne (n : ℕ) : dd (n + 1) ≠ dd n := by
  intro h
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have h1 : (n + 1) % 2 = 1 := by omega
    simp only [dd, hn, h1] at h
    have := congrArg (fun r : Rule M0 => r.val 0) h
    simp at this
  · have h1 : (n + 1) % 2 = 0 := by omega
    simp only [dd, hn, h1] at h
    have := congrArg (fun r : Rule M0 => r.val 0) h
    simp at this

end PitAux

theorem solution : ¬ (∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A)
    (d : ℕ → Rule M) (g h : ℕ → S → ℝ) (hrun : PrintedRun M d g h),
    ∃ N : ℕ, d (N + 1) = d N ∧ IsAverageOptimal (policy M (d N)) ∧
      OptimalityEquations M (g N) (h N)) := by
  intro H
  obtain ⟨N, hN, -⟩ := H PitAux.M0 PitAux.dd PitAux.gg PitAux.hh PitAux.run
  exact PitAux.ne N hN
