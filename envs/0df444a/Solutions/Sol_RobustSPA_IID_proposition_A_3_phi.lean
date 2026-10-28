-- Prove2me | solution 1 for RobustSPA.IID.proposition_A_3_phi
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:37:53.361084+00:00
-- url     : https://prove2.me/submissions/35bde889-ab16-4496-81cc-f1daa8c0d9a3

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

open MeasureTheory RobustSPA.IID

namespace RAffPhi

/-- `w^(n-1) * x^k = w^(n-1-k)` when `w x = 1` and `k ≤ n - 1`. -/
lemma pow_mul_inv_pow {w x : ℝ} (hwx : w * x = 1) {m k : ℕ} (hk : k ≤ m) :
    w ^ m * x ^ k = w ^ (m - k) := by
  have : w ^ m = w ^ (m - k) * w ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [this, mul_assoc, ← mul_pow, hwx, one_pow, mul_one]

/-- The closed form of `Φ*_n` on `(r, ∞)`. -/
noncomputable def g (n : ℕ) (r v : ℝ) : ℝ :=
  (v / (v - r)) ^ (n - 1) * Real.log (v / r) -
    ∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * (v / (v - r)) ^ (n - 1 - k)

lemma phi_eq_g (n : ℕ) (r v : ℝ) (hv : v ∈ Set.Ioc r 1) : PhiStar n r v = g n r v := by
  simp only [PhiStar, if_neg (not_le.mpr hv.1), if_pos hv.2, g]

/-- the series representation -/
lemma phi_series (n : ℕ) (hn : 0 < n) (r : ℝ) (hr0 : 0 < r) (v : ℝ) (hv : v ∈ Set.Ioc r 1) :
    HasSum (fun j : ℕ => 1 / ((j + n : ℕ) : ℝ) * ((v - r) / v) ^ (j + 1)) (PhiStar n r v) := by
  have hv0 : 0 < v := lt_trans hr0 hv.1
  have hvr : 0 < v - r := by linarith [hv.1]
  set x := (v - r) / v with hx
  set w := v / (v - r) with hw
  have hwx : w * x = 1 := by rw [hw, hx]; field_simp
  have hx0 : 0 ≤ x := div_nonneg hvr.le hv0.le
  have hx1 : x < 1 := by rw [hx, div_lt_one hv0]; linarith
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hlog0 := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h1x : 1 - x = r / v := by rw [hx]; field_simp; ring
  have hL : -Real.log (1 - x) = Real.log (v / r) := by
    rw [h1x, Real.log_div hr0.ne' hv0.ne', Real.log_div hv0.ne' hr0.ne']; ring
  rw [hL] at hlog0
  have hshift := (hasSum_nat_add_iff' (n - 1)).mpr hlog0
  have hmul := hshift.mul_left (w ^ (n - 1))
  have hfun : (fun j : ℕ => 1 / ((j + n : ℕ) : ℝ) * x ^ (j + 1)) =
      (fun i : ℕ => w ^ (n - 1) * (x ^ (i + (n - 1) + 1) / (((i + (n - 1) : ℕ) : ℝ) + 1))) := by
    funext j
    have hcast : (((j + (n - 1) : ℕ) : ℝ) + 1) = ((j + n : ℕ) : ℝ) := by
      rw [show j + n = j + (n - 1) + 1 by omega]; push_cast; ring
    rw [hcast, show j + (n - 1) + 1 = (j + 1) + (n - 1) by omega]
    have : w ^ (n - 1) * x ^ (n - 1) = 1 := by rw [← mul_pow, hwx, one_pow]
    calc 1 / ((j + n : ℕ) : ℝ) * x ^ (j + 1)
        = (w ^ (n - 1) * x ^ (n - 1)) * (x ^ (j + 1) / ((j + n : ℕ) : ℝ)) := by rw [this]; ring
      _ = w ^ (n - 1) * (x ^ (j + 1 + (n - 1)) / ((j + n : ℕ) : ℝ)) := by rw [pow_add]; ring
  have hval : PhiStar n r v = w ^ (n - 1) *
      (Real.log (v / r) - ∑ i ∈ Finset.range (n - 1), x ^ (i + 1) / ((i : ℝ) + 1)) := by
    rw [phi_eq_g n r v hv]
    unfold g
    rw [mul_sub, Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n - 1 := Finset.mem_range.mp hi
    rw [show w ^ (n - 1) * (x ^ (i + 1) / ((i : ℝ) + 1)) =
      (w ^ (n - 1) * x ^ (i + 1)) / ((i : ℝ) + 1) by ring, pow_mul_inv_pow hwx (by omega)]
    push_cast
    rw [show n - 1 - (1 + i) = n - 1 - (i + 1) by omega]
    ring
  rw [hfun, hval]
  exact hmul

/-- bounds from the series -/
lemma phi_bounds' (n : ℕ) (hn : 0 < n) (r : ℝ) (hr0 : 0 < r) (v : ℝ) (hv : v ∈ Set.Ioc r 1) :
    0 ≤ PhiStar n r v ∧ PhiStar n r v ≤ (v - r) / (n * r) := by
  have hS := phi_series n hn r hr0 v hv
  have hv0 : 0 < v := lt_trans hr0 hv.1
  set x := (v - r) / v with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith [hv.1]) hv0.le
  have hx1 : x < 1 := by rw [hx, div_lt_one hv0]; linarith [hv.1]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact hS.nonneg fun j => by positivity
  · have hgeo : HasSum (fun j : ℕ => (x / n) * x ^ j) ((x / n) * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
    have hle := hasSum_le (fun j => ?_) hS hgeo
    · have h1x : 1 - x = r / v := by rw [hx]; field_simp; ring
      calc PhiStar n r v ≤ (x / n) * (1 - x)⁻¹ := hle
        _ = (v - r) / (n * r) := by rw [h1x, hx]; field_simp
    · have hjn : (n : ℝ) ≤ ((j + n : ℕ) : ℝ) := by push_cast; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      have hxj : 0 ≤ x ^ (j + 1) := pow_nonneg hx0 _
      calc 1 / ((j + n : ℕ) : ℝ) * x ^ (j + 1) ≤ 1 / (n : ℝ) * x ^ (j + 1) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hnR hjn) hxj
        _ = (x / n) * x ^ j := by rw [pow_succ]; ring

/-- (ODE-Φ) -/
lemma phi_deriv (n : ℕ) (hn : 0 < n) (r : ℝ) (hr0 : 0 < r) (v : ℝ) (hv : v ∈ Set.Ioo r 1) :
    HasDerivAt (PhiStar n r) (1 / v - ((n : ℝ) - 1) * r / (v * (v - r)) * PhiStar n r v) v := by
  have hv0 : 0 < v := lt_trans hr0 hv.1
  have hvr : 0 < v - r := by linarith [hv.1]
  set w := v / (v - r) with hw
  set w' := -r / (v - r) ^ 2 with hw'
  set c := r / (v * (v - r)) with hc
  have hww : w' = -c * w := by rw [hw', hc, hw]; field_simp
  have hW : HasDerivAt (fun u => u / (u - r)) w' v := by
    have := (hasDerivAt_id' v).div ((hasDerivAt_id' v).sub_const r) hvr.ne'
    refine this.congr_deriv ?_
    rw [hw']
    field_simp
    ring
  have hLg : HasDerivAt (fun u => Real.log (u / r)) (1 / v) v := by
    have := ((hasDerivAt_id' v).div_const r).log (div_ne_zero hv0.ne' hr0.ne')
    convert this using 1
    field_simp
  have hS : HasDerivAt (fun u => ∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * (u / (u - r)) ^ (n - 1 - k))
      (∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * (((n - 1 - k : ℕ) : ℝ) * w ^ (n - 1 - k - 1) * w')) v :=
    HasDerivAt.fun_sum fun k _ => (hW.pow (n - 1 - k)).const_mul (1 / (k : ℝ))
  have hG : HasDerivAt (g n r)
      (((n - 1 : ℕ) : ℝ) * w ^ (n - 1 - 1) * w' * Real.log (v / r) + w ^ (n - 1) * (1 / v) -
        ∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * (((n - 1 - k : ℕ) : ℝ) * w ^ (n - 1 - k - 1) * w')) v :=
    ((hW.pow (n - 1)).mul hLg).sub hS
  have hev : PhiStar n r =ᶠ[nhds v] g n r := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with u hu
    exact phi_eq_g n r u ⟨hu.1, hu.2.le⟩
  refine (hG.congr_of_eventuallyEq hev).congr_deriv ?_
  -- algebra
  have hterm : ∀ m : ℕ, (m : ℝ) * w ^ (m - 1) * w' = -c * m * w ^ m := by
    intro m
    rcases m with _ | m
    · simp
    · rw [hww, Nat.add_sub_cancel, pow_succ]; ring
  simp_rw [hterm]
  rw [phi_eq_g n r v ⟨hv.1, hv.2.le⟩]
  unfold g
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  have hsplit : ∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * (-c * ((n - 1 - k : ℕ) : ℝ) * w ^ (n - 1 - k)) =
      -c * ((n : ℝ) - 1) * ∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * w ^ (n - 1 - k) +
        c * ∑ k ∈ Finset.Ico 1 n, w ^ (n - 1 - k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    rw [Nat.cast_sub (show k ≤ n - 1 by omega), hcastn]
    field_simp
    ring
  have hgeo : c * ∑ k ∈ Finset.Ico 1 n, w ^ (n - 1 - k) = (w ^ (n - 1) - 1) / v := by
    have hre : ∑ k ∈ Finset.Ico 1 n, w ^ (n - 1 - k) = ∑ j ∈ Finset.range (n - 1), w ^ j := by
      rw [Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect (fun j => w ^ j) (n - 1)]
      apply Finset.sum_congr rfl
      intro i hi
      have := Finset.mem_range.mp hi
      congr 1
      omega
    have hw1 : w - 1 = r / (v - r) := by rw [hw]; field_simp; ring
    have hwne : w ≠ 1 := by
      intro h; rw [h, sub_self] at hw1
      exact (div_ne_zero hr0.ne' hvr.ne') hw1.symm
    rw [hre, geom_sum_eq hwne, hw1, hc]
    field_simp
  rw [hsplit, hcastn]
  linear_combination (-1 : ℝ) * hgeo

/-- the limit at `r` -/
lemma phi_tendsto (n : ℕ) (hn : 0 < n) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Filter.Tendsto (PhiStar n r) (nhdsWithin r (Set.Ioi r)) (nhds 0) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hup : Filter.Tendsto (fun v : ℝ => (v - r) / (n * r)) (nhdsWithin r (Set.Ioi r)) (nhds 0) := by
    have : Filter.Tendsto (fun v : ℝ => (v - r) / (n * r)) (nhds r) (nhds ((r - r) / (n * r))) :=
      ((continuous_id.sub continuous_const).div_const _).tendsto r
    rw [sub_self, zero_div] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hev : ∀ᶠ v in nhdsWithin r (Set.Ioi r), v ∈ Set.Ioc r 1 := by
    filter_upwards [Ioo_mem_nhdsGT hr1] with v hv
    exact ⟨hv.1, hv.2.le⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hev] with v hv using (phi_bounds' n hn r hr0 v hv).1
  · filter_upwards [hev] with v hv using (phi_bounds' n hn r hr0 v hv).2

/-- `Φ*_n(1) = 1` at the root of the `r*`-equation -/
lemma phi_one (n : ℕ) (hn : 0 < n) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hrEq : rEq n r = 0) :
    PhiStar n r 1 = 1 := by
  rw [phi_eq_g n r 1 ⟨hr1, le_rfl⟩]
  unfold g
  set q := 1 - r with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  set w := 1 / (1 - r) with hw
  have hwq : w * q = 1 := by
    rw [hw, hq, one_div, inv_mul_cancel₀ (by linarith : (1 : ℝ) - r ≠ 0)]
  have hlog : Real.log (1 / r) = q ^ (n - 1) + ∑ k ∈ Finset.Ico 1 n, q ^ k / k := by
    unfold rEq at hrEq
    rw [one_div, Real.log_inv]
    linarith
  rw [hlog, mul_add, pow_mul_inv_pow hwq le_rfl, Nat.sub_self, pow_zero, Finset.mul_sum]
  have : ∑ k ∈ Finset.Ico 1 n, w ^ (n - 1) * (q ^ k / k) =
      ∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * w ^ (n - 1 - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    rw [show w ^ (n - 1) * (q ^ k / k) = (w ^ (n - 1) * q ^ k) / k by ring,
      pow_mul_inv_pow hwq (by omega)]
    ring
  rw [this]
  ring

end RAffPhi

open RAffPhi in
theorem solution (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / n))
    (hrEq : rEq n r = 0) :
    (∀ v ∈ Set.Ioc r 1, HasSum
        (fun j : ℕ => 1 / ((j + n : ℕ) : ℝ) * ((v - r) / v) ^ (j + 1)) (PhiStar n r v)) ∧
      (∀ v ∈ Set.Ioo r 1, HasDerivAt (PhiStar n r)
        (1 / v - ((n : ℝ) - 1) * r / (v * (v - r)) * PhiStar n r v) v) ∧
      Filter.Tendsto (PhiStar n r) (nhdsWithin r (Set.Ioi r)) (nhds 0) ∧
      PhiStar n r 1 = 1 := by
  have hr0 := hr.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : r < 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
    linarith [hr.2]
  exact ⟨fun v hv => phi_series n hn r hr0 v hv, fun v hv => phi_deriv n hn r hr0 v hv,
    phi_tendsto n hn r hr0 hr1, phi_one n hn r hr0 hr1 hrEq⟩
