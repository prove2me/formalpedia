-- Prove2me | solution 1 for UnQuantumMechanics.lax_trace_power_conserved
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:26:39.851436+00:00
-- url     : https://prove2.me/submissions/ba05a91d-ffec-490e-aef6-b49b17d0979c

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

set_option autoImplicit false

lemma lax539c_pow_deriv {m : Type} [Fintype m] [DecidableEq m]
    (H S : ℝ → Matrix m m ℝ)
    (hS : ∀ τ i j, HasDerivAt (fun t => S t i j) ((H τ * S τ - S τ * H τ) i j) τ)
    (k : ℕ) (τ : ℝ) (i j : m) :
    HasDerivAt (fun t => (S t ^ k) i j) ((H τ * S τ ^ k - S τ ^ k * H τ) i j) τ := by
  induction k generalizing i j with
  | zero =>
    have h0 : (H τ * S τ ^ 0 - S τ ^ 0 * H τ) i j = 0 := by simp
    rw [h0]
    simpa using (hasDerivAt_const τ ((1 : Matrix m m ℝ) i j))
  | succ k ih =>
    have hfun : (fun t => (S t ^ (k + 1)) i j)
        = fun t => ∑ l, (S t ^ k) i l * S t l j := by
      funext t
      rw [pow_succ, Matrix.mul_apply]
    rw [hfun]
    have hsum : HasDerivAt (fun t => ∑ l, (S t ^ k) i l * S t l j)
        (∑ l, ((H τ * S τ ^ k - S τ ^ k * H τ) i l * S τ l j
          + (S τ ^ k) i l * (H τ * S τ - S τ * H τ) l j)) τ :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (ih i l).mul (hS τ l j))
    refine hsum.congr_deriv ?_
    have key : H τ * S τ ^ (k + 1) - S τ ^ (k + 1) * H τ
        = (H τ * S τ ^ k - S τ ^ k * H τ) * S τ
          + S τ ^ k * (H τ * S τ - S τ * H τ) := by
      rw [pow_succ]
      noncomm_ring
    rw [key, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]

open Matrix in
theorem solution {m : Type} [Fintype m] [DecidableEq m]
    (H S : ℝ → Matrix m m ℝ)
    (hS : ∀ τ i j, HasDerivAt (fun t => S t i j) ((H τ * S τ - S τ * H τ) i j) τ)
    (k : ℕ) (τ : ℝ) :
    (S τ ^ k).trace = (S 0 ^ k).trace := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t => (S t ^ k).trace) 0 x := by
    intro x
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => lax539c_pow_deriv H S hS k x i i)
    have hz : (∑ i ∈ (Finset.univ : Finset m), (H x * S x ^ k - S x ^ k * H x) i i) = 0 := by
      have : (H x * S x ^ k - S x ^ k * H x).trace = 0 := by
        rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
      simpa [Matrix.trace] using this
    rw [hz] at hsum
    simpa [Matrix.trace] using hsum
  have hc := is_const_of_deriv_eq_zero (f := fun t => (S t ^ k).trace)
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv)
  exact hc τ 0
