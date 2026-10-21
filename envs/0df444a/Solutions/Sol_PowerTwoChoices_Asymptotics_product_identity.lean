-- Prove2me | solution 1 for PowerTwoChoices.Asymptotics.product_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:54:58.277011+00:00
-- url     : https://prove2.me/submissions/06a2317b-4426-4427-ad1d-cd7dc938a04e

import Mathlib
import Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime

set_option autoImplicit false
open Filter Topology

theorem solution (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    HasProd (fun i : ℕ => ∑ k ∈ Finset.range d, lam ^ (k * d ^ i)) (1 / (1 - lam)) := by
  set f : ℕ → ℝ := fun i => ∑ k ∈ Finset.range d, lam ^ (k * d ^ i) with hf
  have hf1 : ∀ i, 1 ≤ f i := by
    intro i
    have := Finset.single_le_sum (f := fun k => lam ^ (k * d ^ i)) (fun k _ => pow_nonneg h0 _)
      (Finset.mem_range.2 (show 0 < d by omega))
    simpa [hf] using this
  have hfpos : ∀ i, 0 < f i := fun i => lt_of_lt_of_le one_pos (hf1 i)
  have h1l : (0 : ℝ) < 1 - lam := by linarith
  -- partial products
  have hprod : ∀ n : ℕ, ∏ i ∈ Finset.range n, f i = (1 - lam ^ (d ^ n)) / (1 - lam) := by
    intro n
    induction n with
    | zero => simp [h1l.ne']
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hy1 : lam ^ (d ^ n) ≠ 1 := by
        have : lam ^ (d ^ n) < 1 := pow_lt_one₀ h0 h1 (by positivity)
        exact this.ne
      have hfn : f n = ((lam ^ (d ^ n)) ^ d - 1) / (lam ^ (d ^ n) - 1) := by
        rw [hf]
        simp only
        rw [← geom_sum_eq hy1 d]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← pow_mul, mul_comm]
      rw [hfn, pow_succ, pow_mul]
      have : lam ^ (d ^ n) - 1 ≠ 0 := sub_ne_zero.2 hy1
      field_simp
      ring
  have hlog : ∀ n : ℕ, ∑ i ∈ Finset.range n, Real.log (f i) =
      Real.log ((1 - lam ^ (d ^ n)) / (1 - lam)) := by
    intro n
    rw [← hprod n, Real.log_prod (fun i _ => (hfpos i).ne')]
  have hlim : Tendsto (fun n : ℕ => lam ^ (d ^ n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega))
  have hlim2 : Tendsto (fun n : ℕ => (1 - lam ^ (d ^ n)) / (1 - lam)) atTop (𝓝 (1 / (1 - lam))) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).div_const (1 - lam)
    simpa using this
  have hlim3 : Tendsto (fun n : ℕ => Real.log ((1 - lam ^ (d ^ n)) / (1 - lam))) atTop
      (𝓝 (Real.log (1 / (1 - lam)))) :=
    hlim2.log (by positivity)
  have hsum : HasSum (fun i => Real.log (f i)) (Real.log (1 / (1 - lam))) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => Real.log_nonneg (hf1 i))]
    simpa only [hlog] using hlim3
  have := Real.hasProd_of_hasSum_log hfpos hsum
  rwa [Real.exp_log (by positivity)] at this
