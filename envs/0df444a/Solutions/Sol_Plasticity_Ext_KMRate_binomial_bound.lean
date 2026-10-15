-- Prove2me | solution 1 for Plasticity.Ext.KMRate.binomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T18:00:49.270694+00:00
-- url     : https://prove2.me/submissions/d75d484b-d612-4564-88a8-4ecc308474d0

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Module

/-!
Krasnosel'skii–Mann iterates with constant step: the binomial bound of
Cominetti–Soto–Vaisman (Israel J. Math. 199 (2014), arXiv:1206.4195, §2.1–2.2),
`‖xₙ - K xₙ‖ ≤ D · E[F(M)]` with `M ~ Bin(n, 2α(1-α))` and `F(m) = C(m, ⌊m/2⌋)/2^m`.

The double-sum recursion (R) of the paper is replaced by its one-step form (the fox-and-hare
race read one hurdle at a time), and the race probabilities are given in closed form:
the hare's survival is a binomial mixture of the survival probabilities of a lazy symmetric
walk, which are binomial mixtures of ballot counts given by the reflection principle.
-/

namespace Sol_Plasticity_Ext_KMRate_binomial_bound

open Finset

/-! ### Binomial sums -/

/-- Pascal's rule inside a binomial sum. -/
lemma pascal_sum (d : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ range (d + 2), ((d + 1).choose k : ℝ) * f k
      = ∑ k ∈ range (d + 1), (d.choose k : ℝ) * (f k + f (k + 1)) := by
  rw [sum_range_succ']
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib,
    Nat.choose_zero_right, Nat.cast_one, one_mul, mul_add]
  have h2 := sum_range_succ' (fun k => (d.choose k : ℝ) * f k) (d + 1)
  rw [sum_range_succ, Nat.choose_succ_self] at h2
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right, Nat.cast_one,
    one_mul] at h2
  linarith

/-- The binomial mixture `∑ₖ C(d,k) pᵏ (1-p)^(d-k) φ(k)`, i.e. `E[φ(Bin(d,p))]`. -/
noncomputable def bmix (p : ℝ) (d : ℕ) (φ : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (d + 1), (d.choose k : ℝ) * p ^ k * (1 - p) ^ (d - k) * φ k

lemma bmix_zero (p : ℝ) (φ : ℕ → ℝ) : bmix p 0 φ = φ 0 := by
  simp [bmix]

/-- Conditioning on the first trial. -/
lemma bmix_succ (p : ℝ) (d : ℕ) (φ : ℕ → ℝ) :
    bmix p (d + 1) φ = (1 - p) * bmix p d φ + p * bmix p d (fun k => φ (k + 1)) := by
  unfold bmix
  have h := pascal_sum d (fun k => p ^ k * (1 - p) ^ (d + 1 - k) * φ k)
  simp only [← mul_assoc] at h
  rw [h, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hk : k ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have e1 : d + 1 - k = (d - k) + 1 := by omega
  have e2 : d + 1 - (k + 1) = d - k := by omega
  rw [e1, e2, pow_succ, pow_succ]
  ring

lemma bmix_const_one (p : ℝ) (d : ℕ) : bmix p d (fun _ => 1) = 1 := by
  unfold bmix
  calc _ = ∑ k ∈ range (d + 1), p ^ k * (1 - p) ^ (d - k) * (d.choose k : ℝ) :=
        sum_congr rfl fun k _ => by ring
    _ = 1 := by rw [← add_pow, add_sub_cancel, one_pow]

/-! ### Ballot counts and the lazy walk -/

/-- The reflection count: the number of `±1` paths of length `m` started at height `h ≥ 0`
that never go below `0` equals `∑ C(m,U)` over `m - h ≤ 2U ≤ m + h + 1`. -/
noncomputable def ballot (h : ℤ) (m : ℕ) : ℝ :=
  ∑ U ∈ range (m + 1),
    (m.choose U : ℝ) * (if (m : ℤ) - h ≤ 2 * U ∧ 2 * (U : ℤ) ≤ m + h + 1 then 1 else 0)

lemma ballot_succ (h : ℤ) (hh : 0 ≤ h) (m : ℕ) :
    ballot h (m + 1) = ballot (h + 1) m + ballot (h - 1) m := by
  unfold ballot
  rw [pascal_sum, ← sum_add_distrib]
  refine sum_congr rfl fun U _ => ?_
  rw [← mul_add]
  congr 1
  push_cast
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma ballot_neg_one (m : ℕ) : ballot (-1) m = 0 := by
  unfold ballot
  refine sum_eq_zero fun U _ => ?_
  rw [if_neg (by omega), mul_zero]

lemma ballot_zero_left (h : ℤ) (hh : 0 ≤ h) : ballot h 0 = 1 := by
  unfold ballot
  simp only [zero_add, range_one, sum_singleton, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.cast_zero, mul_zero]
  rw [if_pos (by omega)]

lemma ballot_zero (m : ℕ) : ballot 0 m = (m.choose (m / 2) : ℝ) := by
  unfold ballot
  rw [sum_eq_single ((m + 1) / 2)]
  · rw [if_pos (by omega), mul_one]
    obtain ⟨k, rfl | rfl⟩ := m.even_or_odd'
    · congr 2; omega
    · have e1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have e2 : (2 * k + 1) / 2 = k := by omega
      rw [e1, e2, Nat.choose_symm_half]
  · intro U _ hU
    rw [if_neg (by omega), mul_zero]
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/-- Survival probability of the lazy symmetric walk (steps `±1` with probability `u/2` each)
started at height `h` for `j` steps: a binomial mixture over the number of moves. -/
noncomputable def walk (u : ℝ) (h : ℤ) (j : ℕ) : ℝ :=
  bmix u j (fun m => ballot h m / 2 ^ m)

lemma walk_succ (u : ℝ) (h : ℤ) (hh : 0 ≤ h) (j : ℕ) :
    walk u h (j + 1) = (1 - u) * walk u h j + u / 2 * (walk u (h + 1) j + walk u (h - 1) j) := by
  unfold walk
  rw [bmix_succ]
  have hs : bmix u j (fun k => ballot h (k + 1) / 2 ^ (k + 1))
      = (bmix u j (fun m => ballot (h + 1) m / 2 ^ m)
          + bmix u j (fun m => ballot (h - 1) m / 2 ^ m)) / 2 := by
    unfold bmix
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun k _ => ?_
    dsimp only
    rw [ballot_succ h hh, pow_succ]
    ring
  rw [hs]
  ring

lemma walk_zero (u : ℝ) (h : ℤ) (hh : 0 ≤ h) : walk u h 0 = 1 := by
  unfold walk
  rw [bmix_zero, ballot_zero_left h hh]
  norm_num

lemma walk_neg_one (u : ℝ) (j : ℕ) : walk u (-1) j = 0 := by
  unfold walk bmix
  refine sum_eq_zero fun m _ => ?_
  simp only [ballot_neg_one, zero_div, mul_zero]

/-! ### The fox-and-hare race, one hurdle at a time -/

/-- `hare a j k` bounds `‖x_j - K x_k‖` for `j ≤ k` (in units of the diameter): the hare runs
from `j` while the fox rests at `k`. It is `E[walk(G, j)]` with `G ~ Bin(k - j, a)`. -/
noncomputable def hare (a : ℝ) (j k : ℕ) : ℝ :=
  bmix a (k - j) (fun g => walk (2 * a * (1 - a)) g j)

/-- `fox a m n` bounds `‖x_m - x_n‖` for `m ≤ n` (in units of the diameter): the fox runs
from `n` while the hare rests at `m`. It equals the paper's `c_{mn}`. -/
noncomputable def fox (a : ℝ) (m n : ℕ) : ℝ :=
  bmix a (n - m) (fun g => walk (2 * a * (1 - a)) ((g : ℤ) - 1) m)

lemma hare_zero (a : ℝ) (k : ℕ) : hare a 0 k = 1 := by
  unfold hare
  have : (fun g : ℕ => walk (2 * a * (1 - a)) g 0) = fun _ => 1 :=
    funext fun g => walk_zero _ _ (Int.natCast_nonneg g)
  rw [Nat.sub_zero, this, bmix_const_one]

lemma fox_self (a : ℝ) (m : ℕ) : fox a m m = 0 := by
  unfold fox
  rw [Nat.sub_self, bmix_zero]
  simp only [Nat.cast_zero, zero_sub, walk_neg_one]

lemma fox_succ (a : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    fox a m (n + 1) = (1 - a) * fox a m n + a * hare a m n := by
  unfold fox hare
  rw [show n + 1 - m = (n - m) + 1 by omega, bmix_succ]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

lemma hare_succ (a : ℝ) {j k : ℕ} (hjk : j + 1 ≤ k) :
    hare a (j + 1) k = (1 - a) * hare a j k + a * fox a j k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + 1 + d := ⟨k - (j + 1), by omega⟩
  unfold hare fox
  rw [show j + 1 + d - j = d + 1 by omega, show j + 1 + d - (j + 1) = d by omega,
    bmix_succ, bmix_succ]
  unfold bmix
  simp only [mul_add, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun g _ => ?_
  rw [walk_succ _ _ (Int.natCast_nonneg g)]
  push_cast
  simp only [add_sub_cancel_right]
  ring

lemma hare_self (a : ℝ) (n : ℕ) :
    hare a n n = ∑ m ∈ range (n + 1),
      (n.choose m : ℝ) * (2 * a * (1 - a)) ^ m * (1 - 2 * a * (1 - a)) ^ (n - m) *
        ((m.choose (m / 2) : ℝ) / 2 ^ m) := by
  unfold hare
  rw [Nat.sub_self, bmix_zero]
  unfold walk bmix
  simp only [Nat.cast_zero, ballot_zero]

/-! ### The normed-space recursion -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_comb_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (v w : E) :
    ‖(1 - a) • v + a • w‖ ≤ (1 - a) * ‖v‖ + a * ‖w‖ := by
  calc _ ≤ ‖(1 - a) • v‖ + ‖a • w‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ha0]

/-- The race bounds along a Krasnosel'skii–Mann orbit `y` with constant step `a`. -/
lemma race_bounds {C : Set E} {D : ℝ} (hD : ∀ x ∈ C, ∀ y ∈ C, ‖x - y‖ ≤ D)
    {K : E → E} (hmaps : Set.MapsTo K C C) (hlip : LipschitzOnWith 1 K C)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {y : ℕ → E}
    (hy : ∀ k, y (k + 1) = (1 - a) • y k + a • K (y k)) (hyC : ∀ k, y k ∈ C) (j : ℕ) :
    (∀ k, j ≤ k → ‖y j - K (y k)‖ ≤ D * hare a j k) ∧
      (∀ n, j ≤ n → ‖y j - y n‖ ≤ D * fox a j n) := by
  have hb : 0 ≤ 1 - a := by linarith
  -- the fox's bounds at level `j` follow from the hare's bounds at level `j`
  have foxpart : ∀ j, (∀ k, j ≤ k → ‖y j - K (y k)‖ ≤ D * hare a j k) →
      ∀ n, j ≤ n → ‖y j - y n‖ ≤ D * fox a j n := by
    intro j hH n hn
    induction n, hn using Nat.le_induction with
    | base => simp [fox_self]
    | succ n hjn ih =>
      have e : y j - y (n + 1) = (1 - a) • (y j - y n) + a • (y j - K (y n)) := by
        rw [hy n]; module
      rw [e, fox_succ a hjn]
      calc _ ≤ (1 - a) * ‖y j - y n‖ + a * ‖y j - K (y n)‖ := norm_comb_le ha0 ha1 _ _
        _ ≤ (1 - a) * (D * fox a j n) + a * (D * hare a j n) :=
            add_le_add (mul_le_mul_of_nonneg_left ih hb)
              (mul_le_mul_of_nonneg_left (hH n hjn) ha0)
        _ = _ := by ring
  induction j with
  | zero =>
    have hH : ∀ k, 0 ≤ k → ‖y 0 - K (y k)‖ ≤ D * hare a 0 k := fun k _ => by
      rw [hare_zero, mul_one]; exact hD _ (hyC 0) _ (hmaps (hyC k))
    exact ⟨hH, foxpart 0 hH⟩
  | succ j ih =>
    have hH : ∀ k, j + 1 ≤ k → ‖y (j + 1) - K (y k)‖ ≤ D * hare a (j + 1) k := by
      intro k hk
      have e : y (j + 1) - K (y k) = (1 - a) • (y j - K (y k)) + a • (K (y j) - K (y k)) := by
        rw [hy j]; module
      have hK : ‖K (y j) - K (y k)‖ ≤ ‖y j - y k‖ := by
        have := hlip.dist_le_mul (y j) (hyC j) (y k) (hyC k)
        simpa [dist_eq_norm] using this
      rw [e, hare_succ a hk]
      calc _ ≤ (1 - a) * ‖y j - K (y k)‖ + a * ‖K (y j) - K (y k)‖ := norm_comb_le ha0 ha1 _ _
        _ ≤ (1 - a) * (D * hare a j k) + a * (D * fox a j k) :=
            add_le_add (mul_le_mul_of_nonneg_left (ih.1 k (by omega)) hb)
              (mul_le_mul_of_nonneg_left (hK.trans (ih.2 k (by omega))) ha0)
        _ = _ := by ring
    exact ⟨hH, foxpart (j + 1) hH⟩

end Normed

end Sol_Plasticity_Ext_KMRate_binomial_bound

open Sol_Plasticity_Ext_KMRate_binomial_bound in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (D : ℝ) (hD : ∀ x ∈ C, ∀ y ∈ C, ‖x - y‖ ≤ D)
    (K : E → E) (hmaps : Set.MapsTo K C C) (hlip : LipschitzOnWith 1 K C)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) (x : E) (hx : x ∈ C) :
    ‖(fun z => (1 - α) • z + α • K z)^[n] x - K ((fun z => (1 - α) • z + α • K z)^[n] x)‖
      ≤ D * ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℝ) * (2 * α * (1 - α)) ^ m * (1 - 2 * α * (1 - α)) ^ (n - m) *
            ((m.choose (m / 2) : ℝ) / 2 ^ m) := by
  set P : E → E := fun z => (1 - α) • z + α • K z with hP
  have hPC : Set.MapsTo P C C := fun z hz =>
    hconv hz (hmaps hz) (by linarith) hα0.le (by ring)
  set y : ℕ → E := fun j => P^[j] x with hydef
  have hy : ∀ j, y (j + 1) = (1 - α) • y j + α • K (y j) := fun j => by
    simp only [hydef]; rw [Function.iterate_succ_apply']
  have hyC : ∀ j, y j ∈ C := fun j => hPC.iterate j hx
  have h := (race_bounds hD hmaps hlip hα0.le hα1.le hy hyC n).1 n le_rfl
  rw [hare_self] at h
  exact h
