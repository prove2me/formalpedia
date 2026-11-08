-- Prove2me | solution 1 for SVFAppt.eq_5_session_end
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:19:56.852087+00:00
-- url     : https://prove2.me/submissions/bbb65b03-8ffa-4012-8a27-826ee0c709be

import Mathlib
import Definitions.Def_SVFAppt_lindley

namespace Aux_Q01_eq_5_session_end
open SVFAppt

noncomputable def Xf {n : ℕ} (τ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then x (τ ⟨i, h⟩) else 0

theorem Xf_lt {n : ℕ} (τ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : ℕ) (h : i < n) :
    Xf τ x i = x (τ ⟨i, h⟩) := by
  unfold Xf
  rw [dif_pos h]

theorem hmax (a : ℝ) : max 0 a - max 0 (-a) = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : -a ≤ 0)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith : (0 : ℝ) ≤ -a)]
    ring

theorem step {n : ℕ} (τ : Equiv.Perm (Fin n)) (x b : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    wait τ x b (k + 1) - idle τ x b (k + 1) =
      wait τ x b k + b (τ ⟨k, hk⟩) - x (τ ⟨k, hk⟩) := by
  have e : lindley τ x b (k + 1) =
      (max 0 ((lindley τ x b k).1 + b (τ ⟨k, hk⟩) - x (τ ⟨k, hk⟩)),
        max 0 (-((lindley τ x b k).1 + b (τ ⟨k, hk⟩) - x (τ ⟨k, hk⟩)))) := by
    show (if h : k < n then
      (max 0 ((lindley τ x b k).1 + b (τ ⟨k, h⟩) - x (τ ⟨k, h⟩)),
        max 0 (-((lindley τ x b k).1 + b (τ ⟨k, h⟩) - x (τ ⟨k, h⟩))))
      else (0, 0)) = _
    rw [dif_pos hk]
  unfold wait idle
  rw [e]
  exact hmax _

theorem tel {n : ℕ} (τ : Equiv.Perm (Fin n)) (x b : Fin n → ℝ) :
    ∀ k, k < n → ∑ i ∈ Finset.range (k + 1), idle τ x b i =
      wait τ x b k - ∑ i ∈ Finset.range k, Xf τ b i + ∑ i ∈ Finset.range k, Xf τ x i := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, sub_zero,
      add_zero]
    rfl
  | succ k ih =>
    intro hk
    have hk' : k < n := by omega
    have h1 := ih hk'
    have h2 := step τ x b k hk'
    rw [Finset.sum_range_succ, h1, Finset.sum_range_succ, Finset.sum_range_succ,
      Xf_lt τ b k hk', Xf_lt τ x k hk']
    linarith

end Aux_Q01_eq_5_session_end

open SVFAppt Aux_Q01_eq_5_session_end in
theorem solution {n : ℕ} (hn : 0 < n) (τ : Equiv.Perm (Fin n)) (x b : Fin n → ℝ) :
    ∑ i : Fin n, idle τ x b i + ∑ j : Fin n, b j =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n), x (τ i)
        + wait τ x b (n - 1) + b (τ ⟨n - 1, by omega⟩) := by
  have hn1 : n - 1 + 1 = n := by omega
  have hidle : ∑ i : Fin n, idle τ x b i = ∑ i ∈ Finset.range n, idle τ x b i :=
    Fin.sum_univ_eq_sum_range (fun i => idle τ x b i) n
  have hbsum : ∑ j : Fin n, b j = ∑ i ∈ Finset.range n, Xf τ b i := by
    rw [← Equiv.sum_comp τ b, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (Xf_lt τ b i i.isLt).symm
  have hfil : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n), x (τ i) =
      ∑ i ∈ Finset.range (n - 1), Xf τ x i := by
    rw [Finset.sum_filter]
    have e1 : ∑ i : Fin n, (if i.val + 1 < n then x (τ i) else 0) =
        ∑ i : Fin n, (fun j : ℕ => if j + 1 < n then Xf τ x j else 0) i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Xf_lt τ x i i.isLt, Fin.eta]
    rw [e1, Fin.sum_univ_eq_sum_range (fun j : ℕ => if j + 1 < n then Xf τ x j else 0) n]
    have e2 := Finset.sum_range_succ (fun j : ℕ => if j + 1 < n then Xf τ x j else 0) (n - 1)
    beta_reduce at e2
    rw [hn1] at e2
    rw [e2, if_neg (lt_irrefl n), add_zero]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  have hI : ∑ i ∈ Finset.range n, idle τ x b i = wait τ x b (n - 1) -
      ∑ i ∈ Finset.range (n - 1), Xf τ b i + ∑ i ∈ Finset.range (n - 1), Xf τ x i := by
    have h := tel τ x b (n - 1) (by omega)
    rw [hn1] at h
    exact h
  have hB : ∑ i ∈ Finset.range n, Xf τ b i =
      ∑ i ∈ Finset.range (n - 1), Xf τ b i + b (τ ⟨n - 1, by omega⟩) := by
    have h := Finset.sum_range_succ (fun i => Xf τ b i) (n - 1)
    rw [hn1, Xf_lt τ b (n - 1) (by omega)] at h
    exact h
  rw [hidle, hbsum, hfil, hI, hB]
  ring
