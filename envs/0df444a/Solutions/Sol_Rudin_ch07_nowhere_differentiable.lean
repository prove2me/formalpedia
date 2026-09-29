-- Prove2me | solution 1 for Rudin.ch07_nowhere_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:25:47.304382+00:00
-- url     : https://prove2.me/submissions/124dcaf2-9728-4b00-a8bd-2ac3317de026

import Mathlib
import Definitions.Def_Rudin_ch07_families

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace RudinLoc

open Filter Topology

/-- The `2`-periodic triangle wave: `phi x = |x|` on `[-1,1]`, extended with period `2`. -/
noncomputable def phi (x : ℝ) : ℝ := |x - 2 * ⌊(x + 1) / 2⌋|

theorem phi_eq (j : ℤ) (x : ℝ) (h1 : 2 * (j : ℝ) - 1 ≤ x) (h2 : x < 2 * j + 1) :
    phi x = |x - 2 * j| := by
  have hf : ⌊(x + 1) / 2⌋ = j := by
    rw [Int.floor_eq_iff]
    refine ⟨by linarith, ?_⟩
    push_cast
    linarith
  rw [phi, hf]

theorem phi_floor (x : ℝ) : phi x = |x - 2 * ⌊(x + 1) / 2⌋| := rfl

theorem phi_bounds (x : ℝ) : 0 ≤ phi x ∧ phi x ≤ 1 := by
  refine ⟨abs_nonneg _, ?_⟩
  have h1 : ((⌊(x + 1) / 2⌋ : ℤ) : ℝ) ≤ (x + 1) / 2 := Int.floor_le _
  have h2 : (x + 1) / 2 < ⌊(x + 1) / 2⌋ + 1 := Int.lt_floor_add_one _
  rw [phi_floor, abs_le]
  constructor <;> linarith

theorem phi_le_of_int (x : ℝ) (m : ℤ) : phi x ≤ |x - 2 * m| := by
  set j : ℤ := ⌊(x + 1) / 2⌋ with hj
  have hb := phi_bounds x
  rcases eq_or_ne m j with rfl | hne
  · exact le_of_eq (phi_floor x)
  · have hd : (1 : ℝ) ≤ |(j : ℝ) - m| := by
      have : (1 : ℤ) ≤ |j - m| := Int.one_le_abs (sub_ne_zero.2 (Ne.symm hne))
      calc (1:ℝ) ≤ ((|j - m| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |(j : ℝ) - m| := by push_cast [Int.cast_abs]; ring_nf
    have h3 : |(2 : ℝ) * j - 2 * m| ≤ |x - 2 * j| + |x - 2 * m| := by
      have : (2 : ℝ) * j - 2 * m = -(x - 2 * j) + (x - 2 * m) := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    have h4 : |(2 : ℝ) * j - 2 * m| = 2 * |(j : ℝ) - m| := by
      rw [show (2 : ℝ) * j - 2 * m = 2 * ((j : ℝ) - m) by ring, abs_mul]
      norm_num
    have h5 : phi x = |x - 2 * j| := phi_floor x
    linarith [hb.2]

theorem phi_lipschitz (s t : ℝ) : |phi s - phi t| ≤ |s - t| := by
  have h1 : phi s ≤ |s - t| + phi t := by
    calc phi s ≤ |s - 2 * (⌊(t + 1) / 2⌋ : ℤ)| := phi_le_of_int s _
      _ = |(s - t) + (t - 2 * (⌊(t + 1) / 2⌋ : ℤ))| := by ring_nf
      _ ≤ |s - t| + |t - 2 * (⌊(t + 1) / 2⌋ : ℤ)| := abs_add_le _ _
      _ = |s - t| + phi t := by rw [phi_floor]
  have h2 : phi t ≤ |s - t| + phi s := by
    calc phi t ≤ |t - 2 * (⌊(s + 1) / 2⌋ : ℤ)| := phi_le_of_int t _
      _ = |(t - s) + (s - 2 * (⌊(s + 1) / 2⌋ : ℤ))| := by ring_nf
      _ ≤ |t - s| + |s - 2 * (⌊(s + 1) / 2⌋ : ℤ)| := abs_add_le _ _
      _ = |s - t| + phi s := by rw [phi_floor, abs_sub_comm]
  rw [abs_le]
  constructor <;> linarith

theorem phi_continuous : Continuous phi := by
  refine LipschitzWith.continuous (K := 1) ?_
  intro s t
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
  have := phi_lipschitz s t
  simp only [ENNReal.coe_one, one_mul]
  exact ENNReal.ofReal_le_ofReal this


/-! ### Periodicity and the affine pieces -/

theorem phi_add_two_int (N : ℤ) (x : ℝ) : phi (x + 2 * N) = phi x := by
  have h1 : ((⌊(x + 1) / 2⌋ : ℤ) : ℝ) ≤ (x + 1) / 2 := Int.floor_le _
  have h2 : (x + 1) / 2 < (⌊(x + 1) / 2⌋ : ℤ) + 1 := Int.lt_floor_add_one _
  set j : ℤ := ⌊(x + 1) / 2⌋
  rw [phi_eq (j + N) (x + 2 * N) (by push_cast; linarith) (by push_cast; linarith),
      phi_eq j x (by linarith) (by linarith)]
  congr 1
  push_cast
  ring

theorem phi_affine (k : ℤ) (y : ℝ) (h1 : (k : ℝ) ≤ y) (h2 : y < k + 1) :
    phi y = if Even k then y - k else (k : ℝ) + 1 - y := by
  rcases Int.even_or_odd k with hk | hk
  · obtain ⟨j, hj⟩ := hk
    subst hj
    rw [if_pos ⟨j, rfl⟩]
    push_cast at h1 h2
    rw [phi_eq j y (by linarith) (by linarith), abs_of_nonneg (by linarith)]
    push_cast
    ring
  · obtain ⟨j, hj⟩ := hk
    subst hj
    rw [if_neg (by simp)]
    push_cast at h1 h2
    rw [phi_eq (j + 1) y (by push_cast; linarith) (by push_cast; linarith)]
    push_cast
    rw [abs_of_nonpos (by linarith)]
    ring

theorem phi_diff (k : ℤ) (s u : ℝ) (hs1 : (k : ℝ) ≤ s) (hs2 : s < k + 1)
    (hu1 : (k : ℝ) ≤ u) (hu2 : u < k + 1) : |phi u - phi s| = |u - s| := by
  rw [phi_affine k s hs1 hs2, phi_affine k u hu1 hu2]
  by_cases h : Even k
  · rw [if_pos h, if_pos h]
    congr 1
    ring
  · rw [if_neg h, if_neg h]
    rw [show ((k : ℝ) + 1 - u) - ((k : ℝ) + 1 - s) = -(u - s) by ring, abs_neg]

/-! ### The Weierstrass-type function -/

noncomputable def F (x : ℝ) : ℝ := ∑' n : ℕ, (3 / 4 : ℝ) ^ n * phi (4 ^ n * x)

theorem summable_terms (x : ℝ) :
    Summable (fun n : ℕ => (3 / 4 : ℝ) ^ n * phi (4 ^ n * x)) := by
  have hg : Summable (fun n : ℕ => (3 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (phi_bounds _).1) (fun n => ?_) hg
  have hb := (phi_bounds (4 ^ n * x)).2
  have hp : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ n := by positivity
  nlinarith

theorem F_continuous : Continuous F := by
  have hg : Summable (fun n : ℕ => (3 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine continuous_tsum (u := fun n : ℕ => (3 / 4 : ℝ) ^ n) (fun n => ?_) hg (fun n x => ?_)
  · exact continuous_const.mul (phi_continuous.comp (continuous_const.mul continuous_id))
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity),
      abs_of_nonneg (phi_bounds _).1]
    have hb := (phi_bounds (4 ^ n * x)).2
    have hp : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ n := by positivity
    nlinarith

theorem F_sub (x d : ℝ) :
    F (x + d) - F x = ∑' n : ℕ, (3 / 4 : ℝ) ^ n * (phi (4 ^ n * (x + d)) - phi (4 ^ n * x)) := by
  rw [F, F, ← Summable.tsum_sub (summable_terms _) (summable_terms _)]
  congr 1
  ext n
  ring


/-! ### The key estimate: arbitrarily large difference quotients at every point -/

theorem key_estimate (x : ℝ) (m : ℕ) :
    ∃ d : ℝ, d ≠ 0 ∧ |d| = 1 / (2 * 4 ^ m) ∧
      ((3 : ℝ) ^ m + 1) / 2 ≤ |(F (x + d) - F x) / d| := by
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  set t : ℝ := 4 ^ m * x with ht
  set k : ℤ := ⌊t⌋ with hk
  have hkt : (k : ℝ) ≤ t := Int.floor_le t
  have htk : t < (k : ℝ) + 1 := Int.lt_floor_add_one t
  set e : ℤ := if t < (k : ℝ) + 1 / 2 then 1 else -1 with he
  set d : ℝ := (e : ℝ) / (2 * 4 ^ m) with hd
  have hae : |(e : ℝ)| = 1 := by
    rw [he]; split <;> norm_num
  have hdabs : |d| = 1 / (2 * 4 ^ m) := by
    rw [hd, abs_div, hae, abs_of_pos (by positivity : (0:ℝ) < 2 * 4 ^ m)]
  have hdpos : 0 < |d| := by rw [hdabs]; positivity
  have hd0 : d ≠ 0 := abs_pos.1 hdpos
  have hscale : (4 : ℝ) ^ m * d = (e : ℝ) / 2 := by
    rw [hd]; field_simp
  have hmx : (4 : ℝ) ^ m * (x + d) = t + (e : ℝ) / 2 := by
    rw [mul_add, hscale, ht]
  -- the term at index `m` has absolute value exactly `1/2`
  have hbm : |phi ((4 : ℝ) ^ m * (x + d)) - phi ((4 : ℝ) ^ m * x)| = 1 / 2 := by
    have hmem : (k : ℝ) ≤ t + (e : ℝ) / 2 ∧ t + (e : ℝ) / 2 < (k : ℝ) + 1 := by
      rcases lt_or_ge t ((k : ℝ) + 1 / 2) with hc | hc
      · have hE : (e : ℝ) = 1 := by rw [he, if_pos hc]; norm_num
        rw [hE]; constructor <;> linarith
      · have hE : (e : ℝ) = -1 := by rw [he, if_neg (not_lt.2 hc)]; norm_num
        rw [hE]; constructor <;> linarith
    rw [hmx, ← ht, phi_diff k t (t + (e : ℝ) / 2) hkt htk hmem.1 hmem.2,
      show t + (e : ℝ) / 2 - t = (e : ℝ) / 2 by ring, abs_div, hae]
    norm_num
  -- terms beyond index `m` vanish by periodicity
  have hvanish : ∀ r : ℕ,
      phi ((4 : ℝ) ^ (m + 1 + r) * (x + d)) - phi ((4 : ℝ) ^ (m + 1 + r) * x) = 0 := by
    intro r
    have harith : (4 : ℝ) ^ (m + 1 + r) * (x + d)
        = (4 : ℝ) ^ (m + 1 + r) * x + 2 * ((e * 4 ^ r : ℤ) : ℝ) := by
      rw [hd]
      push_cast
      rw [pow_add, pow_add]
      field_simp
      ring
    rw [harith, phi_add_two_int]
    ring
  -- Lipschitz bound for every term
  have hlip : ∀ n : ℕ,
      |phi ((4 : ℝ) ^ n * (x + d)) - phi ((4 : ℝ) ^ n * x)| ≤ 4 ^ n * |d| := by
    intro n
    calc |phi ((4 : ℝ) ^ n * (x + d)) - phi ((4 : ℝ) ^ n * x)|
        ≤ |(4 : ℝ) ^ n * (x + d) - 4 ^ n * x| := phi_lipschitz _ _
      _ = 4 ^ n * |d| := by
          rw [show (4 : ℝ) ^ n * (x + d) - 4 ^ n * x = 4 ^ n * d by ring, abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < (4:ℝ) ^ n)]
  -- the series collapses to a finite sum
  have hfin : F (x + d) - F x
      = ∑ n ∈ Finset.range (m + 1),
          (3 / 4 : ℝ) ^ n * (phi ((4 : ℝ) ^ n * (x + d)) - phi ((4 : ℝ) ^ n * x)) := by
    rw [F_sub]
    refine tsum_eq_sum ?_
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    obtain ⟨r, rfl⟩ : ∃ r, n = m + 1 + r := ⟨n - (m + 1), by omega⟩
    rw [hvanish r]
    ring
  rw [Finset.sum_range_succ] at hfin
  set A : ℝ := ∑ n ∈ Finset.range m,
      (3 / 4 : ℝ) ^ n * (phi ((4 : ℝ) ^ n * (x + d)) - phi ((4 : ℝ) ^ n * x)) with hA
  set B : ℝ := (3 / 4 : ℝ) ^ m * (phi ((4 : ℝ) ^ m * (x + d)) - phi ((4 : ℝ) ^ m * x)) with hB
  have hBabs : |B| = (3 / 4 : ℝ) ^ m * (1 / 2) := by
    rw [hB, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (3 / 4 : ℝ) ^ m), hbm]
  have hAabs : |A| ≤ |d| * (((3 : ℝ) ^ m - 1) / 2) := by
    have h1 : |A| ≤ ∑ n ∈ Finset.range m, (3 / 4 : ℝ) ^ n * (4 ^ n * |d|) := by
      rw [hA]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n _ => ?_)
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (3 / 4 : ℝ) ^ n)]
      exact mul_le_mul_of_nonneg_left (hlip n) (by positivity)
    have h3 : ∀ n ∈ Finset.range m,
        (3 / 4 : ℝ) ^ n * (4 ^ n * |d|) = (3 : ℝ) ^ n * |d| := by
      intro n _
      rw [div_pow]
      field_simp
    have h2 : ∑ n ∈ Finset.range m, (3 / 4 : ℝ) ^ n * (4 ^ n * |d|)
        = |d| * (((3 : ℝ) ^ m - 1) / 2) := by
      rw [Finset.sum_congr rfl h3, ← Finset.sum_mul, geom_sum_eq (by norm_num : (3:ℝ) ≠ 1)]
      ring
    linarith
  have htri : |B| ≤ |A + B| + |A| := by
    calc |B| = |(A + B) + -A| := by ring_nf
      _ ≤ |A + B| + |-A| := abs_add_le _ _
      _ = |A + B| + |A| := by rw [abs_neg]
  have hexact : ((3 : ℝ) ^ m + 1) / 2 * |d|
      = (3 / 4 : ℝ) ^ m * (1 / 2) - |d| * (((3 : ℝ) ^ m - 1) / 2) := by
    rw [hdabs, div_pow]
    field_simp
    ring
  have hlow : ((3 : ℝ) ^ m + 1) / 2 * |d| ≤ |F (x + d) - F x| := by
    rw [hfin]
    linarith
  refine ⟨d, hd0, hdabs, ?_⟩
  rw [abs_div, le_div_iff₀ hdpos]
  exact hlow

/-! ### Nowhere differentiability -/

theorem F_not_differentiableAt (x : ℝ) : ¬ DifferentiableAt ℝ F x := by
  intro hdiff
  set L : ℝ := deriv F x with hL
  have hderiv : HasDerivAt F L x := hdiff.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hderiv
  choose D hD0 hDabs hDest using fun m : ℕ => key_estimate x m
  have hb : ∀ m, |D m| = (1 / 2) * (1 / 4 : ℝ) ^ m := by
    intro m
    rw [hDabs m, div_pow, one_pow]
    ring
  have h4 : Tendsto (fun m : ℕ => (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ m) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    simpa using h.const_mul (1 / 2 : ℝ)
  have hneg : Tendsto (fun m : ℕ => -((1 / 2 : ℝ) * (1 / 4 : ℝ) ^ m)) atTop (𝓝 0) := by
    simpa using h4.neg
  have hDzero : Tendsto D atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hneg h4
      (fun m => by rw [← hb m]; exact neg_abs_le _)
      (fun m => by rw [← hb m]; exact le_abs_self _)
  have hy : Tendsto (fun m => x + D m) atTop (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using tendsto_const_nhds.add hDzero
    · filter_upwards with m
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      exact hD0 m (by linarith)
  have hslope := hderiv.comp hy
  rw [Metric.tendsto_atTop] at hslope
  obtain ⟨M, hM⟩ := hslope 1 one_pos
  set m : ℕ := max M (⌈|L|⌉₊ + 1) with hm
  have hmM : M ≤ m := le_max_left _ _
  have hmc : (⌈|L|⌉₊ + 1 : ℕ) ≤ m := le_max_right _ _
  have hLm : |L| < (m : ℝ) := by
    have h1 : |L| ≤ (⌈|L|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈|L|⌉₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hmc
    linarith
  have hbern : 1 + 2 * (m : ℝ) ≤ (3 : ℝ) ^ m := by
    have h := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) m
    norm_num at h
    linarith
  have hdist := hM m hmM
  rw [Real.dist_eq] at hdist
  have hsl : slope F x (x + D m) = (F (x + D m) - F x) / D m := by
    rw [slope_def_field, show x + D m - x = D m by ring]
  have hbig : ((3 : ℝ) ^ m + 1) / 2 ≤ |slope F x (x + D m)| := by
    rw [hsl]; exact hDest m
  have hsmall : |slope F x (x + D m)| < |L| + 1 := by
    have := abs_sub_abs_le_abs_sub (slope F x (x + D m)) L
    simp only [Function.comp_apply] at hdist
    linarith
  linarith

theorem rudin_7_18 : ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x : ℝ, ¬ DifferentiableAt ℝ f x :=
  ⟨F, F_continuous, F_not_differentiableAt⟩

end RudinLoc

theorem solution : ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x : ℝ, ¬ DifferentiableAt ℝ f x :=
  RudinLoc.rudin_7_18
