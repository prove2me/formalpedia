-- Prove2me | solution 1 for TaylorPolyFarBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:13:58.984419+00:00
-- url     : https://prove2.me/submissions/c742b44e-5b17-4a63-a79d-78aee4f10c25

import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_TaylorPolyFarBound

set_option autoImplicit false

theorem _root_.solution (k : ℕ) (σ : ℝ) (hkσ : (k : ℝ) ≤ σ)
    (A : ℝ) (hA : 0 < A) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∀ (v : Plane → ℝ) (S : ℝ), 0 < S → v 0 = 0 →
      (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
          |iteratedFDeriv ℝ j v 0 (fun _ => w)| ≤ A * S ^ (σ - (j : ℝ)) * ‖w‖ ^ j) →
      ∀ y : Plane, τ * S ≤ ‖y‖ →
        |TaylorPoly k v 0 y| ≤ (k : ℝ) * A * τ ^ (-σ) * ‖y‖ ^ σ := by
  intro v S hS hv0 hjet y hy
  have ht0 : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hy
  -- THE FAR-REGIME POWER COMPARISON.  For `0 ≤ a ≤ σ`,
  -- `S ^ (σ - a) * ‖y‖ ^ a ≤ τ ^ (-σ) * ‖y‖ ^ σ`.  The step `τ ^ (-(σ-a)) ≤ τ ^ (-σ)` goes
  -- through `τ ^ (-(σ-a)) = τ ^ (-σ) * τ ^ a` with `τ ^ a ≤ 1`, as pm-0017 directs.
  have hfar : ∀ a : ℝ, 0 ≤ a → a ≤ σ →
      S ^ (σ - a) * ‖y‖ ^ a ≤ τ ^ (-σ) * ‖y‖ ^ σ := by
    intro a ha0 haσ
    have hSle : S ≤ τ⁻¹ * ‖y‖ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hτ0]
      linarith [hy]
    have hpow : (0 : ℝ) ≤ ‖y‖ ^ a := le_of_lt (Real.rpow_pos_of_pos ht0 a)
    have hτs : (0 : ℝ) < τ ^ (-σ) := Real.rpow_pos_of_pos hτ0 _
    calc S ^ (σ - a) * ‖y‖ ^ a
        ≤ (τ⁻¹ * ‖y‖) ^ (σ - a) * ‖y‖ ^ a :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (le_of_lt hS) hSle (by linarith)) hpow
      _ = τ ^ (-(σ - a)) * (‖y‖ ^ (σ - a) * ‖y‖ ^ a) := by
          rw [Real.mul_rpow (le_of_lt (inv_pos.mpr hτ0)) (le_of_lt ht0),
            Real.inv_rpow (le_of_lt hτ0), ← Real.rpow_neg (le_of_lt hτ0)]
          ring
      _ = τ ^ (-(σ - a)) * ‖y‖ ^ σ := by
          rw [← Real.rpow_add ht0]
          ring_nf
      _ = τ ^ (-σ) * τ ^ a * ‖y‖ ^ σ := by
          rw [← Real.rpow_add hτ0]
          ring_nf
      _ ≤ τ ^ (-σ) * 1 * ‖y‖ ^ σ := by
          have h5 : τ ^ a ≤ 1 := Real.rpow_le_one (le_of_lt hτ0) hτ1 ha0
          have hy0 : (0 : ℝ) ≤ ‖y‖ ^ σ := le_of_lt (Real.rpow_pos_of_pos ht0 σ)
          have := mul_le_mul_of_nonneg_left h5 (le_of_lt hτs)
          exact mul_le_mul_of_nonneg_right this hy0
      _ = τ ^ (-σ) * ‖y‖ ^ σ := by ring
  -- unfold the Taylor polynomial and peel the `j = 0` summand, which is `v 0 = 0`
  have hTP : TaylorPoly k v 0 y
      = ∑ j ∈ Finset.range (k + 1), (1 / (Nat.factorial j : ℝ))
          * iteratedFDeriv ℝ j v 0 (fun _ => y - 0) := rfl
  have hf0 : (1 / (Nat.factorial 0 : ℝ)) * iteratedFDeriv ℝ 0 v 0 (fun _ => y - (0 : Plane))
      = 0 := by
    rw [iteratedFDeriv_zero_apply, hv0, mul_zero]
  rw [hTP, Finset.sum_range_succ', hf0, add_zero]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ j ∈ Finset.range k, |(1 / (Nat.factorial (j + 1) : ℝ))
          * iteratedFDeriv ℝ (j + 1) v 0 (fun _ => y - (0 : Plane))|
      ≤ ∑ _j ∈ Finset.range k, A * (τ ^ (-σ) * ‖y‖ ^ σ) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hjk : j + 1 ≤ k := by
          have := Finset.mem_range.mp hj
          omega
        have hjet' := hjet (j + 1) (Nat.le_add_left 1 j) hjk y
        have hfac : (1 / (Nat.factorial (j + 1) : ℝ)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast Nat.factorial_pos (j + 1)
        have hfac0 : (0 : ℝ) ≤ 1 / (Nat.factorial (j + 1) : ℝ) := by positivity
        have hcast : ‖y‖ ^ (j + 1) = ‖y‖ ^ ((j + 1 : ℕ) : ℝ) :=
          (Real.rpow_natCast ‖y‖ (j + 1)).symm
        have hstep : A * S ^ (σ - ((j + 1 : ℕ) : ℝ)) * ‖y‖ ^ (j + 1)
            ≤ A * (τ ^ (-σ) * ‖y‖ ^ σ) := by
          rw [hcast, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hA)
          refine hfar ((j + 1 : ℕ) : ℝ) (by positivity) ?_
          have : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
          linarith
        simp only [sub_zero]
        rw [abs_mul, abs_of_nonneg hfac0]
        calc (1 / (Nat.factorial (j + 1) : ℝ))
              * |iteratedFDeriv ℝ (j + 1) v 0 (fun _ => y)|
            ≤ 1 * |iteratedFDeriv ℝ (j + 1) v 0 (fun _ => y)| :=
              mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
          _ = |iteratedFDeriv ℝ (j + 1) v 0 (fun _ => y)| := one_mul _
          _ ≤ A * S ^ (σ - ((j + 1 : ℕ) : ℝ)) * ‖y‖ ^ (j + 1) := hjet'
          _ ≤ A * (τ ^ (-σ) * ‖y‖ ^ σ) := hstep
    _ = (k : ℝ) * (A * (τ ^ (-σ) * ‖y‖ ^ σ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (k : ℝ) * A * τ ^ (-σ) * ‖y‖ ^ σ := by ring
