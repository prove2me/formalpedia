-- Prove2me | solution 1 for SimpleGraph.exists_cliqueFree_of_sq_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:38.118376+00:00
-- url     : https://prove2.me/submissions/fed6196f-d3aa-4389-b7d6-3df8317e48f2

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Theorems.Thm_SimpleGraph_exists_cliqueFree_of_lt_one
section
@[expose] public section
open Finset
namespace Finset
variable {V : Type*} [DecidableEq V]
end Finset
namespace SimpleGraph
variable {V : Type*} [DecidableEq V]
variable [Fintype V] {p : ℝ}
private theorem two_pow_lt_factorial_sq {k : ℕ} (hk : 3 ≤ k) : 2 ^ (k + 2) < k.factorial ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    have : 2 ≤ (k + 1) ^ 2 := by nlinarith
    nlinarith
end SimpleGraph
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V]
variable [Fintype V] {p : ℝ}
omit [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k)
    (hn : Fintype.card V ^ 2 ≤ 2 ^ k) :
    ∃ G : SimpleGraph V, G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  set n := Fintype.card V
  -- `2 C(n, k) < 2 ^ C(k, 2)`, by squaring
  have hfac : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have hsq : (k.factorial * n.choose k) ^ 2 ≤ 2 ^ (k * k) := by
    calc (k.factorial * n.choose k) ^ 2 ≤ (n ^ k) ^ 2 := Nat.pow_le_pow_left hfac 2
      _ = (n ^ 2) ^ k := by ring
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hn k
      _ = 2 ^ (k * k) := by rw [← pow_mul]
  have hck : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
  have hkey : 2 * n.choose k < 2 ^ k.choose 2 := by
    by_contra hge
    rw [not_lt] at hge
    have h1 : 2 ^ (2 * k.choose 2) ≤ 4 * n.choose k ^ 2 := by
      rw [pow_mul]
      calc (2 ^ 2) ^ k.choose 2 = (2 ^ k.choose 2) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (2 * n.choose k) ^ 2 := Nat.pow_le_pow_left hge 2
        _ = 4 * n.choose k ^ 2 := by ring
    have h2 := two_pow_lt_factorial_sq hk
    have hpos : 0 < k.factorial ^ 2 := by positivity
    -- `2^(k(k-1)) (k!)^2 ≤ 4 (k! C)^2 ≤ 4 · 2^(k k)`, so `(k!)^2 ≤ 4 · 2^k`
    have h3 : 2 ^ (k * (k - 1)) * k.factorial ^ 2 ≤ 4 * 2 ^ (k * k) := by
      calc 2 ^ (k * (k - 1)) * k.factorial ^ 2 ≤ 4 * n.choose k ^ 2 * k.factorial ^ 2 := by
            rw [← hck]; exact Nat.mul_le_mul_right _ h1
        _ = 4 * (k.factorial * n.choose k) ^ 2 := by ring
        _ ≤ 4 * 2 ^ (k * k) := Nat.mul_le_mul_left 4 hsq
    have h4 : 2 ^ (k * k) = 2 ^ (k * (k - 1)) * 2 ^ k := by
      rw [← pow_add]; congr 1
      rcases k with _ | k
      · omega
      · rw [Nat.add_sub_cancel]; ring
    rw [h4] at h3
    have h5 : k.factorial ^ 2 ≤ 4 * 2 ^ k := by
      have hp : 0 < 2 ^ (k * (k - 1)) := by positivity
      nlinarith
    rw [pow_add] at h2
    omega
  refine exists_cliqueFree_of_lt_one (p := 1 / 2) (by norm_num) (by norm_num) ?_
  have hpow : ((1 : ℝ) / 2) ^ k.choose 2 = 1 / 2 ^ k.choose 2 := by rw [div_pow, one_pow]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hpow, ← two_mul, ← mul_assoc,
    mul_one_div, div_lt_one (by positivity)]
  exact_mod_cast hkey
end SimpleGraph
