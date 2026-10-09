-- Prove2me | solution 1 for QueueingFundamentals.BirthDeath.halfin_whitt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T18:23:59.637675+00:00
-- url     : https://prove2.me/submissions/e026af37-e591-402b-92b7-3d40fde8c9a6

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace HW6eee

theorem fac_upper (u v : ℝ) (_hu1 : u ≤ 1) (hv1 : v < 1) :
    (1 - u) / (1 - v) ≤ Real.exp (-u + v / (1 - v)) := by
  have hp : 0 < 1 - v := by linarith
  have h1 : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  have h2 : 1 / (1 - v) ≤ Real.exp (v / (1 - v)) := by
    have := Real.add_one_le_exp (v / (1 - v))
    have e : v / (1 - v) + 1 = 1 / (1 - v) := by field_simp; ring
    linarith
  calc (1 - u) / (1 - v) = (1 - u) * (1 / (1 - v)) := by ring
    _ ≤ Real.exp (-u) * Real.exp (v / (1 - v)) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-u + v / (1 - v)) := (Real.exp_add _ _).symm

theorem fac_lower (u v : ℝ) (hu1 : u < 1) (hv1 : v < 1) :
    Real.exp (-(u / (1 - u)) + v) ≤ (1 - u) / (1 - v) := by
  have hp : 0 < 1 - v := by linarith
  have hq : 0 < 1 - u := by linarith
  have h1 : Real.exp (-(u / (1 - u))) ≤ 1 - u := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hq]
    have := Real.add_one_le_exp (u / (1 - u))
    have e : u / (1 - u) + 1 = (1 - u)⁻¹ := by field_simp; ring
    linarith
  have h2 : Real.exp v ≤ 1 / (1 - v) := by
    rw [le_div_iff₀ hp]
    have h3 := Real.add_one_le_exp (-v)
    have e : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos v]
  calc Real.exp (-(u / (1 - u)) + v) = Real.exp (-(u / (1 - u))) * Real.exp v := Real.exp_add _ _
    _ ≤ (1 - u) * (1 / (1 - v)) := mul_le_mul h1 h2 (Real.exp_pos _).le hq.le
    _ = (1 - u) / (1 - v) := by ring

theorem sum_range_id_real (k : ℕ) : ∑ j ∈ Finset.range k, (j : ℝ) = k * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- the falling product in the staffing sum. -/
noncomputable def Pn (β : ℝ) (n m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (m + 1), (((n : ℝ) - j) / ((n : ℝ) - β * Real.sqrt n))

theorem factor_eq (β : ℝ) (n j : ℕ) (hn : 0 < n) :
    ((n : ℝ) - j) / ((n : ℝ) - β * Real.sqrt n) =
      (1 - (j : ℝ) / n) / (1 - β * Real.sqrt n / n) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [one_sub_div hn', one_sub_div hn', div_div_div_cancel_right₀ hn']

theorem Pn_upper (β : ℝ) (n m : ℕ) (hn : 0 < n) (hm : m < n) (hv : β * Real.sqrt n < n) :
    Pn β n m ≤ Real.exp (-(((m : ℝ) + 1) * m / 2) / n +
      ((m : ℝ) + 1) * ((β * Real.sqrt n / n) / (1 - β * Real.sqrt n / n))) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hv1 : β * Real.sqrt n / n < 1 := by rw [div_lt_one hnr]; exact hv
  have hfac0 : ∀ j ∈ Finset.range (m + 1), 0 ≤ ((n : ℝ) - j) / ((n : ℝ) - β * Real.sqrt n) := by
    intro j hj
    have : j < n := by have := Finset.mem_range.mp hj; omega
    have : (j : ℝ) < n := by exact_mod_cast this
    apply div_nonneg <;> linarith
  unfold Pn
  calc ∏ j ∈ Finset.range (m + 1), (((n : ℝ) - j) / ((n : ℝ) - β * Real.sqrt n))
      ≤ ∏ j ∈ Finset.range (m + 1), Real.exp (-((j : ℝ) / n) +
          (β * Real.sqrt n / n) / (1 - β * Real.sqrt n / n)) := by
        refine Finset.prod_le_prod hfac0 fun j hj => ?_
        have : j < n := by have := Finset.mem_range.mp hj; omega
        have : (j : ℝ) < n := by exact_mod_cast this
        rw [factor_eq β n j hn]
        exact fac_upper _ _ (by rw [div_le_one hnr]; linarith) hv1
    _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div,
          sum_range_id_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem Pn_lower (β : ℝ) (n m : ℕ) (hn : 0 < n) (hm : m < n) (hv : β * Real.sqrt n < n) :
    Real.exp (-(((m : ℝ) + 1) * m / 2) / ((n : ℝ) - m) +
      ((m : ℝ) + 1) * (β * Real.sqrt n / n)) ≤ Pn β n m := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hmr : (m : ℝ) < n := by exact_mod_cast hm
  have hv1 : β * Real.sqrt n / n < 1 := by rw [div_lt_one hnr]; exact hv
  unfold Pn
  calc Real.exp (-(((m : ℝ) + 1) * m / 2) / ((n : ℝ) - m) + ((m : ℝ) + 1) * (β * Real.sqrt n / n))
      = ∏ j ∈ Finset.range (m + 1), Real.exp (-((j : ℝ) / ((n : ℝ) - m)) +
          β * Real.sqrt n / n) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div,
          sum_range_id_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∏ j ∈ Finset.range (m + 1), (((n : ℝ) - j) / ((n : ℝ) - β * Real.sqrt n)) := by
        refine Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) fun j hj => ?_
        have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
        have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
        have hj0 : (0 : ℝ) ≤ j := by positivity
        have hu : (j : ℝ) / n < 1 := by rw [div_lt_one hnr]; linarith
        rw [factor_eq β n j hn]
        refine le_trans ?_ (fac_lower _ _ hu hv1)
        apply Real.exp_le_exp.2
        have e : (j : ℝ) / n / (1 - (j : ℝ) / n) = (j : ℝ) / ((n : ℝ) - j) := by
          field_simp
        rw [e]
        have : (j : ℝ) / ((n : ℝ) - j) ≤ (j : ℝ) / ((n : ℝ) - m) :=
          div_le_div_of_nonneg_left hj0 (by linarith) (by linarith)
        linarith


theorem U_eq (N q β M : ℝ) (hq : 0 < q) (hN : N = q ^ 2) (hb : β < q) :
    -((M + 1) * M / 2) / N + (M + 1) * ((β * q / N) / (1 - β * q / N)) =
      -((M / q) * (M / q + q⁻¹)) / 2 + (M / q + q⁻¹) * (β / (1 - β * q⁻¹)) := by
  subst hN
  have h1 : q - β ≠ 0 := by linarith
  have h2 : 1 - β * q / q ^ 2 = (q - β) / q := by field_simp; try ring
  have h3 : 1 - β * q⁻¹ = (q - β) / q := by field_simp
  rw [h2, h3]
  field_simp
  try ring

theorem L_eq (N q β M : ℝ) (hq : 0 < q) (hN : N = q ^ 2) (hM : M < N) :
    -((M + 1) * M / 2) / (N - M) + (M + 1) * (β * q / N) =
      -((M / q) * (M / q + q⁻¹) / 2) / (1 - (M / q) * q⁻¹) + (M / q + q⁻¹) * β := by
  subst hN
  have h1 : q ^ 2 - M ≠ 0 := by linarith
  have h2 : 1 - (M / q) * q⁻¹ = (q ^ 2 - M) / q ^ 2 := by field_simp
  rw [h2]
  field_simp
  try ring

theorem tendsto_sqrt_nat : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_floor_div (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n) atTop (𝓝 x) := by
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have hlow : Tendsto (fun n : ℕ => x - (Real.sqrt n)⁻¹) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
    rw [le_div_iff₀ hq]
    have := Nat.lt_floor_add_one (x * Real.sqrt n)
    have e : (x - (Real.sqrt n)⁻¹) * Real.sqrt n = x * Real.sqrt n - 1 := by field_simp
    rw [e]; linarith
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop 0] with n hq
    rw [div_le_iff₀ hq]
    exact Nat.floor_le (by positivity)

theorem Pn_pointwise (β x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => Pn β n ⌊x * Real.sqrt n⌋₊) atTop
      (𝓝 (Real.exp (β * x - x ^ 2 / 2))) := by
  have hs : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_sqrt_nat.inv_tendsto_atTop
  have ht := tendsto_floor_div x hx
  set t : ℕ → ℝ := fun n => (⌊x * Real.sqrt n⌋₊ : ℝ) / Real.sqrt n with ht_def
  set s : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ with hs_def
  have hU : Tendsto (fun n => -(t n * (t n + s n)) / 2 + (t n + s n) * (β / (1 - β * s n)))
      atTop (𝓝 (β * x - x ^ 2 / 2)) := by
    have := (((ht.mul (ht.add hs)).div_const 2).neg).add ((ht.add hs).mul
      ((tendsto_const_nhds (x := β)).div ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (hs.const_mul β)) (by simp)))
    have e : β * x - x ^ 2 / 2 = -(x * (x + 0)) / 2 + (x + 0) * (β / (1 - β * 0)) := by
      simp; ring
    rw [e]
    simpa [neg_div] using this
  have hL : Tendsto (fun n => -(t n * (t n + s n) / 2) / (1 - t n * s n) + (t n + s n) * β)
      atTop (𝓝 (β * x - x ^ 2 / 2)) := by
    have := ((((ht.mul (ht.add hs)).div_const 2).neg).div ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (ht.mul hs)) (by simp)).add ((ht.add hs).mul (tendsto_const_nhds (x := β)))
    have e : β * x - x ^ 2 / 2 = -(x * (x + 0) / 2) / (1 - x * 0) + (x + 0) * β := by
      simp; ring
    rw [e]
    exact this
  have hUe := (Real.continuous_exp.tendsto _).comp hU
  have hLe := (Real.continuous_exp.tendsto _).comp hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLe hUe ?_ ?_
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop (max x β)] with n hq
    have hq0 : 0 < Real.sqrt n := lt_of_le_of_lt (le_max_left _ _) hq |>.trans_le' hx
    have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hxq : x < Real.sqrt n := lt_of_le_of_lt (le_max_left _ _) hq
    have hbq : β < Real.sqrt n := lt_of_le_of_lt (le_max_right _ _) hq
    have hn : 0 < n := by
      have : (0 : ℝ) < n := Real.sqrt_pos.1 hq0
      exact_mod_cast this
    have hmr : (⌊x * Real.sqrt n⌋₊ : ℝ) < n := by
      calc (⌊x * Real.sqrt n⌋₊ : ℝ) ≤ x * Real.sqrt n := Nat.floor_le (by positivity)
        _ < Real.sqrt n * Real.sqrt n := mul_lt_mul_of_pos_right hxq hq0
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hm : ⌊x * Real.sqrt n⌋₊ < n := by exact_mod_cast hmr
    have hv : β * Real.sqrt n < n := by
      calc β * Real.sqrt n < Real.sqrt n * Real.sqrt n := mul_lt_mul_of_pos_right hbq hq0
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have := Pn_lower β n _ hn hm hv
    rw [L_eq _ _ β _ hq0 hn2 hmr] at this
    exact this
  · filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop (max x β)] with n hq
    have hq0 : 0 < Real.sqrt n := lt_of_le_of_lt (le_max_left _ _) hq |>.trans_le' hx
    have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hxq : x < Real.sqrt n := lt_of_le_of_lt (le_max_left _ _) hq
    have hbq : β < Real.sqrt n := lt_of_le_of_lt (le_max_right _ _) hq
    have hn : 0 < n := by
      have : (0 : ℝ) < n := Real.sqrt_pos.1 hq0
      exact_mod_cast this
    have hmr : (⌊x * Real.sqrt n⌋₊ : ℝ) < n := by
      calc (⌊x * Real.sqrt n⌋₊ : ℝ) ≤ x * Real.sqrt n := Nat.floor_le (by positivity)
        _ < Real.sqrt n * Real.sqrt n := mul_lt_mul_of_pos_right hxq hq0
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hm : ⌊x * Real.sqrt n⌋₊ < n := by exact_mod_cast hmr
    have hv : β * Real.sqrt n < n := by
      calc β * Real.sqrt n < Real.sqrt n * Real.sqrt n := mul_lt_mul_of_pos_right hbq hq0
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have := Pn_upper β n _ hn hm hv
    rw [U_eq _ _ β _ hq0 hn2 hbq] at this
    exact this


/-- step-function form of the staffing sum. -/
noncomputable def Fn (β : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n,
    (Set.Ico ((m : ℝ) / Real.sqrt n) (((m : ℝ) + 1) / Real.sqrt n)).indicator (fun _ => Pn β n m) x

theorem Fn_eq (β x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n) :
    Fn β n x = if ⌊x * Real.sqrt n⌋₊ < n then Pn β n ⌊x * Real.sqrt n⌋₊ else 0 := by
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hxq : 0 ≤ x * Real.sqrt n := by positivity
  have key : ∀ m : ℕ, (Set.Ico ((m : ℝ) / Real.sqrt n) (((m : ℝ) + 1) / Real.sqrt n)).indicator
      (fun _ => Pn β n m) x = if ⌊x * Real.sqrt n⌋₊ = m then Pn β n m else 0 := by
    intro m
    by_cases h : ⌊x * Real.sqrt n⌋₊ = m
    · rw [if_pos h, Set.indicator_of_mem]
      rw [Set.mem_Ico, div_le_iff₀ hq, lt_div_iff₀ hq]
      have := (Nat.floor_eq_iff hxq).1 h
      exact ⟨this.1, this.2⟩
    · rw [if_neg h, Set.indicator_of_notMem]
      intro hmem
      rw [Set.mem_Ico, div_le_iff₀ hq, lt_div_iff₀ hq] at hmem
      exact h ((Nat.floor_eq_iff hxq).2 ⟨hmem.1, hmem.2⟩)
  unfold Fn
  simp_rw [key]
  simp only [Finset.sum_ite_eq, Finset.mem_range]

theorem Fn_meas (β : ℝ) (n : ℕ) : Measurable (Fn β n) := by
  unfold Fn
  exact Finset.measurable_sum _ fun m _ => measurable_const.indicator measurableSet_Ico

theorem Fn_integral (β : ℝ) (n : ℕ) (hn : 0 < n) :
    ∫ x in Set.Ici (0 : ℝ), Fn β n x = (Real.sqrt n)⁻¹ * ∑ m ∈ Finset.range n, Pn β n m := by
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  unfold Fn
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hsub : Set.Ico ((m : ℝ) / Real.sqrt n) (((m : ℝ) + 1) / Real.sqrt n) ⊆ Set.Ici 0 := by
      intro y hy
      exact le_trans (by positivity) hy.1
    have hle : (m : ℝ) / Real.sqrt n ≤ ((m : ℝ) + 1) / Real.sqrt n :=
      div_le_div_of_nonneg_right (by linarith) hq.le
    rw [integral_indicator_const _ measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
      Set.inter_eq_left.2 hsub, Real.volume_real_Ico_of_le hle, smul_eq_mul]
    field_simp
    try ring
  · intro m _
    refine Integrable.restrict ?_
    exact (integrable_indicator_iff measurableSet_Ico).2
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

theorem Fn_bound (β : ℝ) (hβ : 0 < β) (n : ℕ) (hq : max 1 (2 * β) ≤ Real.sqrt n) (x : ℝ)
    (hx : 0 ≤ x) : ‖Fn β n x‖ ≤ Real.exp (-x ^ 2 / 2 + x / 2 + 2 * β * (x + 1)) := by
  have hq1 : 1 ≤ Real.sqrt n := le_trans (le_max_left _ _) hq
  have hqb : 2 * β ≤ Real.sqrt n := le_trans (le_max_right _ _) hq
  have hq0 : 0 < Real.sqrt n := by linarith
  have hn : 0 < n := by
    have : (0 : ℝ) < n := Real.sqrt_pos.1 hq0
    exact_mod_cast this
  rw [Fn_eq β x hx n hn]
  split_ifs with hm
  · have hbq : β < Real.sqrt n := by linarith
    have hv : β * Real.sqrt n < n := by
      calc β * Real.sqrt n < Real.sqrt n * Real.sqrt n := mul_lt_mul_of_pos_right hbq hq0
        _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hP0 : 0 ≤ Pn β n ⌊x * Real.sqrt n⌋₊ :=
      (Real.exp_pos _).le.trans (Pn_lower β n _ hn hm hv)
    rw [Real.norm_eq_abs, abs_of_nonneg hP0]
    refine (Pn_upper β n _ hn hm hv).trans ?_
    rw [U_eq _ _ β _ hq0 hn2 hbq]
    apply Real.exp_le_exp.2
    set q := Real.sqrt n
    set M : ℝ := (⌊x * q⌋₊ : ℝ)
    set t := M / q
    set s := q⁻¹
    have hs0 : 0 < s := inv_pos.2 hq0
    have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ hq1
    have hbs : β * s ≤ 1 / 2 := by
      rw [show β * s = β / q from rfl, div_le_iff₀ hq0]; linarith
    have ht0 : 0 ≤ t := by positivity
    have htx : t ≤ x := by
      rw [div_le_iff₀ hq0]; exact Nat.floor_le (by positivity)
    have hxts : x ≤ t + s := by
      have e : t + s = (M + 1) / q := by
        show M / q + q⁻¹ = (M + 1) / q
        field_simp
      rw [e, le_div_iff₀ hq0]
      exact (Nat.lt_floor_add_one (x * q)).le
    have h1 : β / (1 - β * s) ≤ 2 * β := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : (t + s) * (β / (1 - β * s)) ≤ (t + s) * (2 * β) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3a : t * x ≤ t * (t + s) := mul_le_mul_of_nonneg_left hxts ht0
    have h3b : (x - s) * x ≤ t * x := mul_le_mul_of_nonneg_right (by linarith) hx
    have h4 : s * x ≤ x := mul_le_of_le_one_left hx hs1
    have h5 : (t + s) * (2 * β) ≤ (x + 1) * (2 * β) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  · rw [norm_zero]; positivity

theorem bound_integrable (β : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2 + x / 2 + 2 * β * (x + 1)))
      (volume.restrict (Set.Ici 0)) := by
  set b : ℝ := 2 * β + 1 / 2
  have hg := ((integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).comp_sub_right b).const_mul
    (Real.exp (2 * β + b ^ 2 / 2))
  refine (hg.congr (ae_of_all _ fun x => ?_)).restrict
  simp only
  rw [← Real.exp_add]
  congr 1
  simp only [b]
  ring

theorem staffing_core (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * ∑ m ∈ Finset.range n, Pn β n m)
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), Real.exp (β * x - x ^ 2 / 2))) := by
  rw [← integral_Ici_eq_integral_Ioi]
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Set.Ici 0))
    (l := atTop) (F := fun n x => Fn β n x) (f := fun x => Real.exp (β * x - x ^ 2 / 2))
    (fun x => Real.exp (-x ^ 2 / 2 + x / 2 + 2 * β * (x + 1)))
    (Eventually.of_forall fun n => (Fn_meas β n).aestronglyMeasurable)
    (by
      filter_upwards [tendsto_sqrt_nat.eventually_ge_atTop (max 1 (2 * β))] with n hq
      exact ae_restrict_of_forall_mem measurableSet_Ici fun x hx => Fn_bound β hβ n hq x hx)
    (bound_integrable β)
    (by
      refine ae_restrict_of_forall_mem measurableSet_Ici fun x hx => ?_
      have hx' : (0 : ℝ) ≤ x := hx
      refine (Pn_pointwise β x hx').congr' ?_
      filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop x] with n hq
      have hq0 : 0 < Real.sqrt n := lt_of_le_of_lt hx' hq
      have hn : 0 < n := by
        have : (0 : ℝ) < n := Real.sqrt_pos.1 hq0
        exact_mod_cast this
      have hmr : (⌊x * Real.sqrt n⌋₊ : ℝ) < n := by
        calc (⌊x * Real.sqrt n⌋₊ : ℝ) ≤ x * Real.sqrt n := Nat.floor_le (by positivity)
          _ < Real.sqrt n * Real.sqrt n := mul_lt_mul_of_pos_right hq hq0
          _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
      have hm : ⌊x * Real.sqrt n⌋₊ < n := by exact_mod_cast hmr
      show Pn β n ⌊x * Real.sqrt n⌋₊ = Fn β n x
      rw [Fn_eq β x hx' n hn, if_pos hm])
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact Fn_integral β n hn

end HW6eee

namespace HW6eee

/-- descending product times the remaining factorial. -/
theorem prod_sub_mul_fact (c : ℕ) : ∀ k : ℕ, k ≤ c →
    (∏ j ∈ Finset.range k, ((c : ℝ) - j)) * ((c - k).factorial : ℝ) = (c.factorial : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ c := by omega
    have h1 : c - k = (c - (k + 1)) + 1 := by omega
    have h2 := ih hk'
    rw [h1, Nat.factorial_succ] at h2
    rw [Finset.prod_range_succ]
    have h3 : (((c - (k + 1)) + 1 : ℕ) : ℝ) = (c : ℝ) - k := by
      rw [← h1, Nat.cast_sub hk']
    push_cast at h2 h3 ⊢
    rw [← h2, ← h3]
    ring

theorem prod_ratio_eq (c n : ℕ) (hn : n < c) (r : ℝ) (hr : 0 < r) :
    ∏ j ∈ Finset.range (c - 1 - n + 1), (((c : ℝ) - j) / r) =
      r ^ n / (n.factorial : ℝ) * ((c.factorial : ℝ) / r ^ c) := by
  have hk : c - 1 - n + 1 = c - n := by omega
  rw [hk, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hP := prod_sub_mul_fact c (c - n) (by omega)
  have hcn : c - (c - n) = n := by omega
  rw [hcn] at hP
  have hfn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hpow : r ^ c = r ^ n * r ^ (c - n) := by rw [← pow_add]; congr 1; omega
  have hP' : ∏ j ∈ Finset.range (c - n), ((c : ℝ) - j) = (c.factorial : ℝ) / n.factorial := by
    rw [eq_div_iff hfn, hP]
  rw [hP', hpow]
  have : r ^ n ≠ 0 := by positivity
  have : r ^ (c - n) ≠ 0 := by positivity
  field_simp

end HW6eee

namespace QueueingFundamentals.BirthDeath

open Filter Topology

/-- H3: the Erlang C formula in "falling-product" form. -/
theorem erlangC_eq_inv (c : ℕ) (hc : 1 ≤ c) (r : ℝ) (hr0 : 0 < r) (hrc : r < c) :
    erlangC c r = 1 / (1 + (1 - r / c) *
      ∑ m ∈ Finset.range c, ∏ j ∈ Finset.range (m + 1), (((c : ℝ) - j) / r)) := by
  have hT : ∑ m ∈ Finset.range c, ∏ j ∈ Finset.range (m + 1), (((c : ℝ) - j) / r) =
      (∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ)) * ((c.factorial : ℝ) / r ^ c) := by
    rw [← Finset.sum_range_reflect, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact HW6eee.prod_ratio_eq c n (Finset.mem_range.mp hn) r hr0
  rw [hT]
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have h1 : 0 < 1 - r / c := by rw [sub_pos, div_lt_one hcpos]; exact hrc
  have hf : (0 : ℝ) < c.factorial := by positivity
  have hrc' : 0 < r ^ c := by positivity
  have hS : 0 ≤ ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ) :=
    Finset.sum_nonneg fun n _ => by positivity
  unfold erlangC
  set S := ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ)
  set q := 1 - r / c
  have hA : 0 < r ^ c / ((c.factorial : ℝ) * q) := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp

/-- H2: Erlang C is monotone in the offered load on `(0, c)`. -/
theorem erlangC_monotoneOn (c : ℕ) (hc : 1 ≤ c) : MonotoneOn (erlangC c) (Set.Ioo 0 (c : ℝ)) := by
  intro r hr s hs hrs
  rw [erlangC_eq_inv c hc r hr.1 hr.2, erlangC_eq_inv c hc s hs.1 hs.2]
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hq : 0 ≤ 1 - s / c := by
    rw [sub_nonneg, div_le_one hcpos]; exact hs.2.le
  have hqq : 1 - s / c ≤ 1 - r / c := by
    have : r / c ≤ s / c := div_le_div_of_nonneg_right hrs hcpos.le
    linarith
  have hfac : ∀ m ∈ Finset.range c, ∀ j ∈ Finset.range (m + 1), (0 : ℝ) ≤ (c : ℝ) - j := by
    intro m hm j hj
    have : j < c := by
      have := Finset.mem_range.mp hm; have := Finset.mem_range.mp hj; omega
    have : (j : ℝ) < c := by exact_mod_cast this
    linarith
  have hsum : ∑ m ∈ Finset.range c, ∏ j ∈ Finset.range (m + 1), (((c : ℝ) - j) / s) ≤
      ∑ m ∈ Finset.range c, ∏ j ∈ Finset.range (m + 1), (((c : ℝ) - j) / r) := by
    refine Finset.sum_le_sum fun m hm => ?_
    refine Finset.prod_le_prod (fun j hj => div_nonneg (hfac m hm j hj) hs.1.le) fun j hj => ?_
    exact div_le_div_of_nonneg_left (hfac m hm j hj) hr.1 hrs
  have hsum0 : 0 ≤ ∑ m ∈ Finset.range c, ∏ j ∈ Finset.range (m + 1), (((c : ℝ) - j) / s) :=
    Finset.sum_nonneg fun m hm =>
      Finset.prod_nonneg fun j hj => div_nonneg (hfac m hm j hj) hs.1.le
  have hX : (1 - s / c) * ∑ m ∈ Finset.range c, ∏ j ∈ Finset.range (m + 1), (((c : ℝ) - j) / s) ≤
      (1 - r / c) * ∑ m ∈ Finset.range c, ∏ j ∈ Finset.range (m + 1), (((c : ℝ) - j) / r) :=
    mul_le_mul hqq hsum hsum0 (by linarith)
  apply one_div_le_one_div_of_le
  · have := mul_nonneg hq hsum0; linarith
  · linarith

/-- H5: Mills-ratio identity. -/
theorem gaussian_mills (β : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (β * x - x ^ 2 / 2) =
      ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β /
        ProbabilityTheory.gaussianPDFReal 0 1 β := by
  set g : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2) with hg
  have key : ∀ x : ℝ, Real.exp (β * x - x ^ 2 / 2) = Real.exp (β ^ 2 / 2) * g (x - β) := by
    intro x; simp only [hg]; rw [← Real.exp_add]; congr 1; ring
  simp_rw [key]
  rw [integral_const_mul]
  have hshift : ∫ x in Set.Ioi (0 : ℝ), g (x - β) = ∫ x in Set.Ioi (-β), g x := by
    have := (measurePreserving_sub_right volume β).setIntegral_preimage_emb
      (measurableEmbedding_subRight β) g (Set.Ioi (-β))
    rw [← this]
    congr 1
    ext x; simp
  have hneg : ∫ x in Set.Ioi (-β), g x = ∫ x in Set.Iic β, g x := by
    have := integral_comp_neg_Ioi (-β) g
    rw [neg_neg] at this
    rw [← this]
    congr 1; ext x; simp [hg]
  have hcdf : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β =
      (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x in Set.Iic β, g x := by
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def,
      ProbabilityTheory.gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
        fun x _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)]
    rw [← integral_const_mul]
    congr 1; ext x
    simp [ProbabilityTheory.gaussianPDFReal, hg]
  have hpdf : ProbabilityTheory.gaussianPDFReal 0 1 β =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(β ^ 2) / 2) := by
    simp [ProbabilityTheory.gaussianPDFReal]
  rw [hshift, hneg, hcdf, hpdf, show -(β ^ 2) / 2 = -(β ^ 2 / 2) by ring, Real.exp_neg]
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have he0 : 0 < Real.exp (β ^ 2 / 2) := Real.exp_pos _
  rw [eq_div_iff (by positivity)]
  field_simp

end QueueingFundamentals.BirthDeath

namespace HW6eee

open ProbabilityTheory

theorem gauss_int : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
  have := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only; congr 1; ring

theorem cdf_std_eq (β : ℝ) : cdf (gaussianReal 0 1) β =
    (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x in Set.Iic β, Real.exp (-(x ^ 2) / 2) := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  rw [← integral_const_mul]
  congr 1; ext x
  simp [gaussianPDFReal]

theorem pdf_std_eq (β : ℝ) : gaussianPDFReal 0 1 β =
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(β ^ 2) / 2) := by
  simp [gaussianPDFReal]

theorem cdf_std_pos (β : ℝ) : 0 < cdf (gaussianReal 0 1) β := by
  rw [cdf_eq_real, measureReal_def]
  apply ENNReal.toReal_pos
  · intro h
    have h2 := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
    rw [Real.volume_Iic] at h2
    exact ENNReal.top_ne_zero h2
  · exact measure_ne_top _ _

theorem cdf_std_cont : Continuous (cdf (gaussianReal 0 1)) := by
  have hint := gauss_int
  have h : ∀ β : ℝ, cdf (gaussianReal 0 1) β = (Real.sqrt (2 * Real.pi))⁻¹ *
      ((∫ x in Set.Iic 0, Real.exp (-(x ^ 2) / 2)) + ∫ x in (0 : ℝ)..β, Real.exp (-(x ^ 2) / 2)) := by
    intro β
    rw [cdf_std_eq, ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
    ring
  rw [funext h]
  exact continuous_const.mul (continuous_const.add
    (intervalIntegral.continuous_primitive (fun a b => hint.intervalIntegrable) 0))

end HW6eee

namespace QueueingFundamentals.BirthDeath

open Filter Topology ProbabilityTheory

/-- H1: shape of `α(β)` on `(0, ∞)`. -/
theorem halfinWhittAlpha_props :
    (∀ β : ℝ, 0 < β → 0 < halfinWhittAlpha β ∧ halfinWhittAlpha β < 1) ∧
      StrictAntiOn halfinWhittAlpha (Set.Ioi 0) ∧ ContinuousOn halfinWhittAlpha (Set.Ioi 0) ∧
      Tendsto halfinWhittAlpha (𝓝[>] 0) (𝓝 1) ∧ Tendsto halfinWhittAlpha atTop (𝓝 0) := by
  have hαdef : ∀ β, halfinWhittAlpha β = gaussianPDFReal 0 1 β /
      (gaussianPDFReal 0 1 β + β * cdf (gaussianReal 0 1) β) := fun _ => rfl
  have hφpos : ∀ β, 0 < gaussianPDFReal 0 1 β := fun β => gaussianPDFReal_pos 0 1 β one_ne_zero
  have hΦpos := HW6eee.cdf_std_pos
  have hΦcont := HW6eee.cdf_std_cont
  have hΦmono := monotone_cdf (gaussianReal 0 1)
  have hφcont : Continuous (gaussianPDFReal 0 1) := by
    rw [funext HW6eee.pdf_std_eq]; fun_prop
  have hs : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  refine ⟨fun β hβ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hαdef]
    have h1 := hφpos β
    have h2 := mul_pos hβ (hΦpos β)
    exact ⟨div_pos h1 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    rw [hαdef, hαdef]
    have hφa := hφpos a
    have hφb := hφpos b
    have hΦa := hΦpos a
    have hΦab : cdf (gaussianReal 0 1) a ≤ cdf (gaussianReal 0 1) b := hΦmono hab.le
    have hφlt : gaussianPDFReal 0 1 b < gaussianPDFReal 0 1 a := by
      rw [HW6eee.pdf_std_eq, HW6eee.pdf_std_eq]
      apply mul_lt_mul_of_pos_left _ hs
      apply Real.exp_lt_exp.2
      nlinarith
    rw [div_lt_div_iff₀ (by nlinarith [hΦpos b]) (by nlinarith)]
    have h1 : gaussianPDFReal 0 1 b * a < gaussianPDFReal 0 1 a * b := by nlinarith
    have h2 : gaussianPDFReal 0 1 b * a * cdf (gaussianReal 0 1) a <
        gaussianPDFReal 0 1 a * b * cdf (gaussianReal 0 1) b := by
      calc gaussianPDFReal 0 1 b * a * cdf (gaussianReal 0 1) a
          < gaussianPDFReal 0 1 a * b * cdf (gaussianReal 0 1) a := mul_lt_mul_of_pos_right h1 hΦa
        _ ≤ gaussianPDFReal 0 1 a * b * cdf (gaussianReal 0 1) b :=
          mul_le_mul_of_nonneg_left hΦab (by positivity)
    nlinarith
  · have : halfinWhittAlpha = fun β => gaussianPDFReal 0 1 β /
        (gaussianPDFReal 0 1 β + β * cdf (gaussianReal 0 1) β) := funext hαdef
    rw [this]
    refine hφcont.continuousOn.div (hφcont.add (continuous_id.mul hΦcont)).continuousOn ?_
    intro β hβ
    have := mul_pos (Set.mem_Ioi.mp hβ) (hΦpos β)
    have := hφpos β
    show gaussianPDFReal 0 1 β + β * cdf (gaussianReal 0 1) β ≠ 0
    linarith
  · have hc : ContinuousAt halfinWhittAlpha 0 := by
      have : halfinWhittAlpha = fun β => gaussianPDFReal 0 1 β /
          (gaussianPDFReal 0 1 β + β * cdf (gaussianReal 0 1) β) := funext hαdef
      rw [this]
      refine hφcont.continuousAt.div (hφcont.add (continuous_id.mul hΦcont)).continuousAt ?_
      show gaussianPDFReal 0 1 0 + 0 * cdf (gaussianReal 0 1) 0 ≠ 0
      rw [zero_mul, add_zero]; exact (hφpos 0).ne'
    have h0 : halfinWhittAlpha 0 = 1 := by
      rw [hαdef]; simp [(hφpos 0).ne']
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [h0] at this
  · have hφlim : Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
      rw [funext HW6eee.pdf_std_eq]
      have h1 : Tendsto (fun β : ℝ => -(β ^ 2) / 2) atTop atBot :=
        Filter.Tendsto.atBot_div_const (by norm_num)
          (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
      have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (Real.sqrt (2 * Real.pi))⁻¹
      simpa using h2
    have hup := hφlim.div_const (cdf (gaussianReal 0 1) 1)
    rw [zero_div] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with β hβ
      rw [hαdef]
      have := hφpos β
      have := mul_pos hβ (hΦpos β)
      positivity
    · filter_upwards [eventually_ge_atTop 1] with β hβ
      rw [hαdef]
      have h1 := hΦpos 1
      have h2 : cdf (gaussianReal 0 1) 1 ≤ cdf (gaussianReal 0 1) β := hΦmono hβ
      have h3 := hφpos β
      apply div_le_div_of_nonneg_left h3.le h1
      nlinarith

end QueueingFundamentals.BirthDeath

namespace HW6eee

open QueueingFundamentals.BirthDeath ProbabilityTheory

theorem core (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => erlangC n ((n : ℝ) - β * Real.sqrt n)) atTop
      (𝓝 (halfinWhittAlpha β)) := by
  have hS := staffing_core β hβ
  rw [gaussian_mills β] at hS
  have hφ := gaussianPDFReal_pos 0 1 β one_ne_zero
  have hIpos : 0 < cdf (gaussianReal 0 1) β / gaussianPDFReal 0 1 β := div_pos (cdf_std_pos β) hφ
  have hlim : Tendsto (fun n : ℕ => 1 / (1 + β * ((Real.sqrt n)⁻¹ *
      ∑ m ∈ Finset.range n, Pn β n m))) atTop
      (𝓝 (1 / (1 + β * (cdf (gaussianReal 0 1) β / gaussianPDFReal 0 1 β)))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add (hS.const_mul β)) (by positivity)
  have hval : halfinWhittAlpha β =
      1 / (1 + β * (cdf (gaussianReal 0 1) β / gaussianPDFReal 0 1 β)) := by
    unfold halfinWhittAlpha
    field_simp
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [tendsto_sqrt_nat.eventually_gt_atTop β] with n hq
  have hq0 : 0 < Real.sqrt n := hβ.trans hq
  have hn0 : (0 : ℝ) < n := Real.sqrt_pos.1 hq0
  have hn1 : 1 ≤ n := by
    have : 0 < n := by exact_mod_cast hn0
    omega
  have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hr0 : 0 < (n : ℝ) - β * Real.sqrt n := by
    nlinarith [mul_lt_mul_of_pos_right hq hq0]
  have hrn : (n : ℝ) - β * Real.sqrt n < n := by nlinarith [mul_pos hβ hq0]
  rw [erlangC_eq_inv n hn1 _ hr0 hrn]
  have e : ∀ q : ℝ, 0 < q → q * q = (n : ℝ) → 1 - ((n : ℝ) - β * q) / n = β * q⁻¹ := by
    intro q hq hqq
    rw [← hqq]
    field_simp
    try ring
  rw [e _ hq0 hnn]
  unfold Pn
  ring

end HW6eee

namespace QueueingFundamentals.BirthDeath

open Filter Topology

theorem halfin_whitt_main (r : ℕ → ℝ) (hr : ∀ n : ℕ, 1 ≤ n → 0 < r n ∧ r n < n) :
    (∀ β : ℝ, 0 < β → 0 < halfinWhittAlpha β ∧ halfinWhittAlpha β < 1) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∃! β : ℝ, 0 < β ∧ halfinWhittAlpha β = α) ∧
      ∀ β : ℝ, 0 < β →
        (Tendsto (fun n : ℕ => erlangC n (r n)) atTop (𝓝 (halfinWhittAlpha β)) ↔
          Tendsto (fun n : ℕ => ((n : ℝ) - r n) / Real.sqrt n) atTop (𝓝 β)) := by
  obtain ⟨h1, hanti, hcont, h0, hinf⟩ := halfinWhittAlpha_props
  refine ⟨h1, fun α hα0 hα1 => ?_, fun β hβ => ?_⟩
  · obtain ⟨x0, hx0a, hx0⟩ := ((h0.eventually (lt_mem_nhds hα1)).and self_mem_nhdsWithin).exists
    obtain ⟨x1, hx1a, hx1⟩ :=
      ((hinf.eventually (gt_mem_nhds hα0)).and (eventually_gt_atTop x0)).exists
    have hx0' : (0 : ℝ) < x0 := hx0
    have hsub : Set.Icc x0 x1 ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le hx0' hy.1
    obtain ⟨c, hc, hca⟩ := intermediate_value_Icc' hx1.le (hcont.mono hsub) ⟨hx1a.le, hx0a.le⟩
    have hc0 : (0 : ℝ) < c := lt_of_lt_of_le hx0' hc.1
    refine ⟨c, ⟨hc0, hca⟩, fun y hy => ?_⟩
    exact hanti.injOn (Set.mem_Ioi.2 hy.1) (Set.mem_Ioi.2 hc0) (hy.2.trans hca.symm)
  · have hcore := HW6eee.core
    have cmp : ∀ n : ℕ, 1 ≤ n → ∀ γ : ℝ, 0 < γ → γ < Real.sqrt n →
        ((((n : ℝ) - r n) / Real.sqrt n ≤ γ →
            erlangC n ((n : ℝ) - γ * Real.sqrt n) ≤ erlangC n (r n)) ∧
          (γ ≤ ((n : ℝ) - r n) / Real.sqrt n →
            erlangC n (r n) ≤ erlangC n ((n : ℝ) - γ * Real.sqrt n))) := by
      intro n hn γ hγ hγn
      have hq0 : 0 < Real.sqrt n := hγ.trans hγn
      have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
      obtain ⟨hr0, hrn⟩ := hr n hn
      have hK0 : 0 < (n : ℝ) - γ * Real.sqrt n := by
        nlinarith [mul_lt_mul_of_pos_right hγn hq0]
      have hKn : (n : ℝ) - γ * Real.sqrt n < n := by nlinarith [mul_pos hγ hq0]
      have hmono := erlangC_monotoneOn n hn
      constructor
      · intro hy
        apply hmono ⟨hK0, hKn⟩ ⟨hr0, hrn⟩
        rw [div_le_iff₀ hq0] at hy
        linarith
      · intro hy
        apply hmono ⟨hr0, hrn⟩ ⟨hK0, hKn⟩
        rw [le_div_iff₀ hq0] at hy
        linarith
    constructor
    · intro hC
      rw [tendsto_order]
      constructor
      · intro b' hb'
        have hb''pos : 0 < max b' (β / 2) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
        have hb''lt : max b' (β / 2) < β := max_lt hb' (by linarith)
        have hgt : halfinWhittAlpha β < halfinWhittAlpha (max b' (β / 2)) :=
          hanti (Set.mem_Ioi.2 hb''pos) (Set.mem_Ioi.2 hβ) hb''lt
        have hm1 : halfinWhittAlpha β <
            (halfinWhittAlpha β + halfinWhittAlpha (max b' (β / 2))) / 2 := by linarith
        have hm2 : (halfinWhittAlpha β + halfinWhittAlpha (max b' (β / 2))) / 2 <
            halfinWhittAlpha (max b' (β / 2)) := by linarith
        filter_upwards [hC.eventually (gt_mem_nhds hm1),
          (hcore _ hb''pos).eventually (lt_mem_nhds hm2), eventually_ge_atTop 1,
          HW6eee.tendsto_sqrt_nat.eventually_gt_atTop (max b' (β / 2))] with n hCn hKn hn1 hqn
        by_contra hy
        replace hy := not_lt.mp hy
        have := (cmp n hn1 _ hb''pos hqn).1 (hy.trans (le_max_left _ _))
        linarith
      · intro b' hb'
        have hb0 : 0 < b' := hβ.trans hb'
        have hlt : halfinWhittAlpha b' < halfinWhittAlpha β :=
          hanti (Set.mem_Ioi.2 hβ) (Set.mem_Ioi.2 hb0) hb'
        have hm1 : (halfinWhittAlpha β + halfinWhittAlpha b') / 2 < halfinWhittAlpha β := by
          linarith
        have hm2 : halfinWhittAlpha b' < (halfinWhittAlpha β + halfinWhittAlpha b') / 2 := by
          linarith
        filter_upwards [hC.eventually (lt_mem_nhds hm1),
          (hcore _ hb0).eventually (gt_mem_nhds hm2), eventually_ge_atTop 1,
          HW6eee.tendsto_sqrt_nat.eventually_gt_atTop b'] with n hCn hKn hn1 hqn
        by_contra hy
        replace hy := not_lt.mp hy
        have := (cmp n hn1 _ hb0 hqn).2 hy
        linarith
    · intro hy
      rw [tendsto_order]
      constructor
      · intro a' ha'
        have hev : ∀ᶠ x in 𝓝 β, a' < halfinWhittAlpha x :=
          (hcont.continuousAt (Ioi_mem_nhds hβ)).eventually (lt_mem_nhds ha')
        obtain ⟨γ, hγβ, hγ⟩ := hev.exists_gt
        have hγ0 : 0 < γ := hβ.trans hγβ
        filter_upwards [(hcore γ hγ0).eventually (lt_mem_nhds hγ), hy.eventually (gt_mem_nhds hγβ),
          eventually_ge_atTop 1, HW6eee.tendsto_sqrt_nat.eventually_gt_atTop γ]
          with n hK hyn hn1 hqn
        have := (cmp n hn1 γ hγ0 hqn).1 hyn.le
        linarith
      · intro a' ha'
        have hev : ∀ᶠ x in 𝓝 β, halfinWhittAlpha x < a' ∧ 0 < x :=
          ((hcont.continuousAt (Ioi_mem_nhds hβ)).eventually (gt_mem_nhds ha')).and
            (lt_mem_nhds hβ)
        obtain ⟨γ, hγβ, hγ, hγ0⟩ := hev.exists_lt
        filter_upwards [(hcore γ hγ0).eventually (gt_mem_nhds hγ), hy.eventually (lt_mem_nhds hγβ),
          eventually_ge_atTop 1, HW6eee.tendsto_sqrt_nat.eventually_gt_atTop γ]
          with n hK hyn hn1 hqn
        have := (cmp n hn1 γ hγ0 hqn).2 hyn.le
        linarith

end QueueingFundamentals.BirthDeath

open QueueingFundamentals.BirthDeath Filter Topology in
theorem solution (r : ℕ → ℝ) (hr : ∀ n : ℕ, 1 ≤ n → 0 < r n ∧ r n < n) :
    (∀ β : ℝ, 0 < β → 0 < halfinWhittAlpha β ∧ halfinWhittAlpha β < 1) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∃! β : ℝ, 0 < β ∧ halfinWhittAlpha β = α) ∧
      ∀ β : ℝ, 0 < β →
        (Tendsto (fun n : ℕ => erlangC n (r n)) atTop (𝓝 (halfinWhittAlpha β)) ↔
          Tendsto (fun n : ℕ => ((n : ℝ) - r n) / Real.sqrt n) atTop (𝓝 β)) := by
  exact halfin_whitt_main r hr
