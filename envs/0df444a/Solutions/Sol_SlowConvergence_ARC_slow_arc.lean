-- Prove2me | solution 1 for SlowConvergence.ARC.slow_arc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T08:41:21.442899+00:00
-- url     : https://prove2.me/submissions/f69df55c-9251-4bf0-9d85-baf97d3f91ff

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Method

set_option autoImplicit false

namespace SlowArcAux

open Filter Topology SlowConvergence.ARC
open scoped ContDiff

noncomputable def Tr (y : ℝ) : ℝ := Real.smoothTransition (2 * y - 1 / 2)
noncomputable def Pl (y : ℝ) : ℝ := Real.smoothTransition (2 - 256 * y ^ 2)
noncomputable def Wt (y : ℝ) : ℝ := -Tr y - y * Pl y

theorem Wt_smooth : ContDiff ℝ ∞ Wt := by
  have h1 : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hA : ContDiff ℝ ∞ (fun y : ℝ => Real.smoothTransition (2 * y - 1 / 2)) :=
    h1.comp (by fun_prop)
  have hB : ContDiff ℝ ∞ (fun y : ℝ => Real.smoothTransition (2 - 256 * y ^ 2)) :=
    h1.comp (by fun_prop)
  exact hA.neg.sub (contDiff_id.mul hB)

theorem Wt_left (y : ℝ) (hy : y < -1 / 11) : Wt y = 0 := by
  have h1 : Tr y = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  have h2 : Pl y = 0 := Real.smoothTransition.zero_of_nonpos (by nlinarith)
  simp [Wt, h1, h2]

theorem Wt_right (y : ℝ) (hy : 3 / 4 ≤ y) : Wt y = -1 := by
  have h1 : Tr y = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  have h2 : Pl y = 0 := Real.smoothTransition.zero_of_nonpos (by nlinarith)
  simp [Wt, h1, h2]

theorem Wt_mid (y : ℝ) (hy : |y| ≤ 1 / 16) : Wt y = -y := by
  rw [abs_le] at hy
  have h1 : Tr y = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  have h2 : Pl y = 1 := Real.smoothTransition.one_of_one_le (by nlinarith)
  simp [Wt, h1, h2]

theorem Wt_ge (y : ℝ) : -2 ≤ Wt y := by
  have hT : Tr y ≤ 1 := Real.smoothTransition.le_one _
  have hP0 : 0 ≤ Pl y := Real.smoothTransition.nonneg _
  have hP1 : Pl y ≤ 1 := Real.smoothTransition.le_one _
  have : y * Pl y ≤ 1 := by
    rcases le_or_gt y 0 with h | h
    · nlinarith
    · rcases le_or_gt y 1 with h' | h'
      · nlinarith
      · have h2 : Pl y = 0 := Real.smoothTransition.zero_of_nonpos (by nlinarith)
        rw [h2]; norm_num
  unfold Wt; linarith

theorem iter_Wt_zero (n : ℕ) : ∀ y : ℝ, (y < -1 / 11 ∨ 3 / 4 < y) → deriv^[n + 1] Wt y = 0 := by
  induction n with
  | zero =>
    intro y hy
    simp only [zero_add, Function.iterate_one]
    rcases hy with hy | hy
    · have hev : Wt =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hy] with z hz using Wt_left z hz
      rw [hev.deriv_eq]; simp
    · have hev : Wt =ᶠ[𝓝 y] fun _ => (-1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hy] with z hz using Wt_right z (le_of_lt hz)
      rw [hev.deriv_eq]; simp
  | succ n ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    have hev : deriv^[n + 1] Wt =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      rcases hy with hy | hy
      · filter_upwards [Iio_mem_nhds hy] with z hz using ih z (Or.inl hz)
      · filter_upwards [Ioi_mem_nhds hy] with z hz using ih z (Or.inr hz)
    rw [hev.deriv_eq]; simp

theorem iter_Wt_bound (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |deriv^[n + 1] Wt y| ≤ B := by
  have hc : Continuous (deriv^[n + 1] Wt) :=
    (ContDiff.iterate_deriv (n + 1) Wt_smooth).continuous
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 / 11 : ℝ)) (b := 3 / 4)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (-1 / 11 : ℝ) (3 / 4)
  · have := hC y hy
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have hy' : y < -1 / 11 ∨ 3 / 4 < y := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      exact hy
    rw [iter_Wt_zero n y hy', abs_zero]
    exact le_max_right _ _

variable (τ : ℝ)

noncomputable def stp (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1)) ^ (1 / (3 - 2 * τ))

noncomputable def xs (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, stp τ j

noncomputable def Sm (G : ℝ → ℝ) (m : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, m k * G ((x - xs τ k) / stp τ k)

noncomputable def Fn (x : ℝ) : ℝ := ∑' k : ℕ, stp τ k ^ 3 * Wt ((x - xs τ k) / stp τ k)

theorem stp_pos (k : ℕ) : 0 < stp τ k := Real.rpow_pos_of_pos (by positivity) _

theorem stp_le_one (hτ1 : τ < 1) (k : ℕ) : stp τ k ≤ 1 := by
  unfold stp
  apply Real.rpow_le_one (by positivity)
  · rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  · apply div_nonneg zero_le_one; linarith

theorem stp_anti (hτ1 : τ < 1) {j k : ℕ} (hjk : j ≤ k) : stp τ k ≤ stp τ j := by
  unfold stp
  apply Real.rpow_le_rpow (by positivity)
  · apply one_div_le_one_div_of_le (by positivity)
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  · apply div_nonneg zero_le_one; linarith

theorem stp_ge (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ stp τ k := by
  unfold stp
  have h := Real.rpow_le_rpow_of_exponent_ge (x := 1 / ((k : ℝ) + 1)) (y := 1)
    (z := 1 / (3 - 2 * τ)) (by positivity)
    (by rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    (by rw [div_le_one (by linarith)]; linarith)
  rwa [Real.rpow_one] at h

theorem xs_succ (k : ℕ) : xs τ (k + 1) = xs τ k + stp τ k := by
  simp [xs, Finset.sum_range_succ]

theorem xs_mono {j k : ℕ} (hjk : j ≤ k) : xs τ j ≤ xs τ k := by
  unfold xs
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hjk)
  intro i _ _; exact (stp_pos τ i).le

theorem xs_gap {j k : ℕ} (hjk : j < k) : xs τ j + stp τ j ≤ xs τ k := by
  rw [← xs_succ]; exact xs_mono τ hjk

theorem xs_unbdd (hτ0 : 0 < τ) (hτ1 : τ < 1) (X : ℝ) : ∃ N, X < xs τ N := by
  obtain ⟨N, hN⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop X).exists
  refine ⟨N, lt_of_lt_of_le hN ?_⟩
  unfold xs
  exact Finset.sum_le_sum fun i _ => stp_ge τ hτ0 hτ1 i

theorem Fn_eq_Sm (hτ1 : τ < 1) (N : ℕ) (x : ℝ) (hx : x < xs τ N - stp τ N / 8) :
    Fn τ x = Sm τ Wt (fun k => stp τ k ^ 3) N x := by
  unfold Fn Sm
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  have h1 := xs_mono τ hk
  have h2 := stp_anti τ hτ1 hk
  have hp := stp_pos τ k
  have : (x - xs τ k) / stp τ k < -1 / 11 := by
    rw [div_lt_iff₀ hp]; nlinarith
  rw [Wt_left _ this, mul_zero]

theorem Fn_ev (hτ0 : 0 < τ) (hτ1 : τ < 1) (x : ℝ) :
    ∃ N, Fn τ =ᶠ[𝓝 x] Sm τ Wt (fun k => stp τ k ^ 3) N := by
  obtain ⟨N, hN⟩ := xs_unbdd τ hτ0 hτ1 (x + 1)
  have h1 := stp_le_one τ hτ1 N
  have hx : x < xs τ N - stp τ N / 8 := by linarith
  refine ⟨N, ?_⟩
  filter_upwards [Iio_mem_nhds hx] with z hz using Fn_eq_Sm τ hτ1 N z hz

theorem Sm_smooth (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ → ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (Sm τ G m N) := by
  unfold Sm
  apply ContDiff.sum
  intro k _
  exact contDiff_const.mul (hG.comp (by fun_prop))

theorem deriv_Sm (G : ℝ → ℝ) (hG : Differentiable ℝ G) (m : ℕ → ℝ) (N : ℕ) :
    deriv (Sm τ G m N) = Sm τ (deriv G) (fun k => m k / stp τ k) N := by
  funext x
  unfold Sm
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum (A := fun k x => m k * G ((x - xs τ k) / stp τ k))
  intro k _
  have h1 : HasDerivAt (fun x : ℝ => (x - xs τ k) / stp τ k) (1 / stp τ k) x :=
    ((hasDerivAt_id' x).sub_const (xs τ k)).div_const (stp τ k)
  have h2 := ((hG ((x - xs τ k) / stp τ k)).hasDerivAt.comp x h1).const_mul (m k)
  exact h2.congr_deriv (by beta_reduce; ring)

theorem Fn_smooth (hτ0 : 0 < τ) (hτ1 : τ < 1) : ContDiff ℝ ∞ (Fn τ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨N, hN⟩ := Fn_ev τ hτ0 hτ1 x
  exact (Sm_smooth τ Wt Wt_smooth _ N).contDiffAt.congr_of_eventuallyEq hN

theorem sep (hτ1 : τ < 1) {j k : ℕ} (hjk : j < k) (x : ℝ)
    (hj : (x - xs τ j) / stp τ j ≤ 3 / 4) (hk : -1 / 11 ≤ (x - xs τ k) / stp τ k) : False := by
  have pj := stp_pos τ j
  have pk := stp_pos τ k
  rw [div_le_iff₀ pj] at hj
  rw [le_div_iff₀ pk] at hk
  have h1 := xs_gap τ hjk
  have h2 := stp_anti τ hτ1 hjk.le
  nlinarith

theorem Sm_bound (hτ1 : τ < 1) (V : ℝ → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hV0 : ∀ y, (y < -1 / 11 ∨ 3 / 4 < y) → V y = 0) (hB : ∀ y, |V y| ≤ B)
    (m : ℕ → ℝ) (hm : ∀ k, |m k| ≤ 1) (N : ℕ) (x : ℝ) : |Sm τ V m N x| ≤ B := by
  have hsupp : ∀ k, V ((x - xs τ k) / stp τ k) ≠ 0 →
      -1 / 11 ≤ (x - xs τ k) / stp τ k ∧ (x - xs τ k) / stp τ k ≤ 3 / 4 := by
    intro k hk
    by_contra hc
    apply hk
    apply hV0
    rcases not_and_or.1 hc with h | h
    · left; exact lt_of_not_ge h
    · right; exact lt_of_not_ge h
  by_cases hex : ∃ k ∈ Finset.range N, V ((x - xs τ k) / stp τ k) ≠ 0
  · obtain ⟨k0, hk0, hne⟩ := hex
    unfold Sm
    rw [Finset.sum_eq_single k0]
    · rw [abs_mul]
      calc |m k0| * |V ((x - xs τ k0) / stp τ k0)| ≤ 1 * B :=
            mul_le_mul (hm k0) (hB _) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    · intro j _ hjk
      by_cases hz : V ((x - xs τ j) / stp τ j) = 0
      · rw [hz, mul_zero]
      · exfalso
        have a0 := hsupp k0 hne
        have a1 := hsupp j hz
        rcases lt_or_gt_of_ne hjk with h | h
        · exact sep τ hτ1 h x a1.2 a0.1
        · exact sep τ hτ1 h x a0.2 a1.1
    · intro h; exact absurd hk0 h
  · push_neg at hex
    unfold Sm
    rw [Finset.sum_eq_zero (fun k hk => by rw [hex k hk, mul_zero]), abs_zero]
    exact hB0

theorem Wt_diff1 : Differentiable ℝ Wt := Wt_smooth.differentiable (by simp)

theorem Wt_diff2 : Differentiable ℝ (deriv Wt) := by
  have := ContDiff.iterate_deriv 1 Wt_smooth
  simp only [Function.iterate_one] at this
  exact this.differentiable (by simp)

theorem Wt_diff3 : Differentiable ℝ (deriv (deriv Wt)) := by
  have := ContDiff.iterate_deriv 2 Wt_smooth
  exact this.differentiable (by simp)

theorem dd_eq (hτ0 : 0 < τ) (hτ1 : τ < 1) (y : ℝ) : ∃ N,
    deriv (deriv (Fn τ)) y =
      Sm τ (deriv (deriv Wt)) (fun k => stp τ k ^ 3 / stp τ k / stp τ k) N y ∧
    deriv (deriv (deriv (Fn τ))) y =
      Sm τ (deriv (deriv (deriv Wt))) (fun k => stp τ k ^ 3 / stp τ k / stp τ k / stp τ k) N y := by
  obtain ⟨N, hev⟩ := Fn_ev τ hτ0 hτ1 y
  have e1 := hev.deriv
  rw [deriv_Sm τ Wt Wt_diff1] at e1
  have e2 := e1.deriv
  rw [deriv_Sm τ (deriv Wt) Wt_diff2] at e2
  refine ⟨N, e2.eq_of_nhds, ?_⟩
  have e3 := e2.deriv_eq
  rw [deriv_Sm τ (deriv (deriv Wt)) Wt_diff3] at e3
  exact e3

theorem Fn_near (hτ1 : τ < 1) (k : ℕ) (x : ℝ) (hx : |x - xs τ k| < stp τ k / 16) :
    Fn τ x = -(∑ j ∈ Finset.range k, stp τ j ^ 3) - stp τ k ^ 2 * (x - xs τ k) := by
  have pk := stp_pos τ k
  have hk1 := stp_anti τ hτ1 (Nat.le_succ k)
  rw [abs_lt] at hx
  have hxN : x < xs τ (k + 1) - stp τ (k + 1) / 8 := by
    rw [xs_succ]; linarith
  rw [Fn_eq_Sm τ hτ1 (k + 1) x hxN]
  unfold Sm
  rw [Finset.sum_range_succ]
  have hrest : ∑ j ∈ Finset.range k, stp τ j ^ 3 * Wt ((x - xs τ j) / stp τ j)
      = ∑ j ∈ Finset.range k, -(stp τ j ^ 3) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have pj := stp_pos τ j
    have g1 := xs_gap τ hj
    have g2 := stp_anti τ hτ1 hj.le
    have : 3 / 4 ≤ (x - xs τ j) / stp τ j := by
      rw [le_div_iff₀ pj]; nlinarith
    rw [Wt_right _ this]; ring
  have hmid : Wt ((x - xs τ k) / stp τ k) = -((x - xs τ k) / stp τ k) := by
    apply Wt_mid
    rw [abs_div, abs_of_pos pk, div_le_iff₀ pk, abs_le]
    constructor <;> linarith
  rw [hrest, hmid, Finset.sum_neg_distrib]
  field_simp
  ring

theorem Fn_ev_aff (hτ1 : τ < 1) (k : ℕ) :
    Fn τ =ᶠ[𝓝 (xs τ k)]
      fun x => -(∑ j ∈ Finset.range k, stp τ j ^ 3) - stp τ k ^ 2 * (x - xs τ k) := by
  have hp : 0 < stp τ k / 16 := by have := stp_pos τ k; positivity
  filter_upwards [Metric.ball_mem_nhds (xs τ k) hp] with z hz
  rw [Metric.mem_ball, Real.dist_eq] at hz
  exact Fn_near τ hτ1 k z hz

theorem aff_deriv (C a c : ℝ) : deriv (fun x : ℝ => C - a * (x - c)) = fun _ => -a := by
  funext x
  have := (((hasDerivAt_id' x).sub_const c).const_mul a).const_sub C
  simpa using this.deriv

theorem Fn_at (hτ1 : τ < 1) (k : ℕ) :
    Fn τ (xs τ k) = -(∑ j ∈ Finset.range k, stp τ j ^ 3) := by
  have := (Fn_ev_aff τ hτ1 k).eq_of_nhds
  rw [this]; ring

theorem dFn_at (hτ1 : τ < 1) (k : ℕ) : deriv (Fn τ) (xs τ k) = -(stp τ k ^ 2) := by
  rw [(Fn_ev_aff τ hτ1 k).deriv_eq, aff_deriv]

theorem ddFn_at (hτ1 : τ < 1) (k : ℕ) : deriv (deriv (Fn τ)) (xs τ k) = 0 := by
  have e := (Fn_ev_aff τ hτ1 k).deriv
  rw [aff_deriv] at e
  rw [e.deriv_eq]; simp

theorem model_eq (hτ1 : τ < 1) (k : ℕ) (s : ℝ) :
    model (Fn τ) 1 (xs τ k) s
      = -(∑ j ∈ Finset.range k, stp τ j ^ 3) - stp τ k ^ 2 * s + |s| ^ 3 / 3 := by
  unfold model
  rw [Fn_at τ hτ1, dFn_at τ hτ1, ddFn_at τ hτ1]
  ring

theorem rho_eq (hτ1 : τ < 1) (k : ℕ) : rho (Fn τ) 1 (xs τ k) (stp τ k) = 3 / 2 := by
  have pk := stp_pos τ k
  unfold rho
  rw [← xs_succ]
  have e1 : Fn τ (xs τ k) - Fn τ (xs τ (k + 1)) = stp τ k ^ 3 := by
    rw [Fn_at τ hτ1, Fn_at τ hτ1, Finset.sum_range_succ]; ring
  have e2 : Fn τ (xs τ k) - model (Fn τ) 1 (xs τ k) (stp τ k) = 2 / 3 * stp τ k ^ 3 := by
    rw [model_eq τ hτ1, Fn_at τ hτ1, abs_of_pos pk]; ring
  rw [e1, e2, div_eq_iff (by positivity)]
  ring

theorem model_min (hτ1 : τ < 1) (k : ℕ) (s' : ℝ) :
    model (Fn τ) 1 (xs τ k) (stp τ k) ≤ model (Fn τ) 1 (xs τ k) s' := by
  have pk := stp_pos τ k
  rw [model_eq τ hτ1, model_eq τ hτ1, abs_of_pos pk]
  rcases le_or_gt 0 s' with hs | hs
  · rw [abs_of_nonneg hs]
    nlinarith [mul_nonneg (sq_nonneg (s' - stp τ k)) (by linarith : (0 : ℝ) ≤ s' + 2 * stp τ k)]
  · rw [abs_of_neg hs]
    nlinarith [pow_pos pk 3, mul_nonneg (sq_nonneg (stp τ k)) (neg_nonneg.2 hs.le),
      pow_pos (neg_pos.2 hs) 3]

theorem summable_stp3 (hτ0 : 0 < τ) (hτ1 : τ < 1) : Summable (fun k => stp τ k ^ 3) := by
  have hp : 1 < 3 * (1 / (3 - 2 * τ)) := by
    rw [mul_one_div, one_lt_div (by linarith)]; linarith
  have h1 := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 hp)
  refine h1.congr (fun n => ?_)
  unfold stp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.div_rpow zero_le_one
    (by positivity), Real.one_rpow]
  push_cast
  congr 2
  ring

theorem Fn_bdd (hτ0 : 0 < τ) (hτ1 : τ < 1) : BddBelow (Set.range (Fn τ)) := by
  refine ⟨-2 * ∑' k, stp τ k ^ 3, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨N, hN⟩ := xs_unbdd τ hτ0 hτ1 (x + 1)
  have h1 := stp_le_one τ hτ1 N
  rw [Fn_eq_Sm τ hτ1 N x (by linarith)]
  unfold Sm
  have hs := (summable_stp3 τ hτ0 hτ1).sum_le_tsum (Finset.range N)
    (fun i _ => by have := stp_pos τ i; positivity)
  have h2 : ∑ k ∈ Finset.range N, stp τ k ^ 3 * (-2) ≤
      ∑ k ∈ Finset.range N, stp τ k ^ 3 * Wt ((x - xs τ k) / stp τ k) := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (Wt_ge _) (by have := stp_pos τ k; positivity)
  rw [← Finset.sum_mul] at h2
  linarith

theorem main (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
      (∃ M : ℝ, ∀ y, |deriv (deriv f) y| ≤ M) ∧
      (∃ L : NNReal, LipschitzWith L (deriv (deriv f))) ∧
      ∃ x s σ : ℕ → ℝ, x 0 = 0 ∧ σ 0 = 1 ∧
        (∀ γ₁ γ₂ η₁ η₂ : ℝ, 1 < γ₁ → γ₁ ≤ γ₂ → 0 < η₁ → η₁ ≤ η₂ → η₂ < 1 →
          IsARCRun f γ₁ γ₂ η₁ η₂ x s σ ∧ ∀ k, η₂ < rho f (σ k) (x k) (s k)) ∧
        (∀ k : ℕ, |deriv f (x k)| = (1 / ((k : ℝ) + 1)) ^ (2 / (3 - 2 * τ))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, |deriv f (x k)| ≤ ε →
          (⌊ε ^ (-(3 / 2 - τ))⌋₊ : ℝ) ≤ k + 1) := by
  have hsm := Fn_smooth τ hτ0 hτ1
  have hgrad : ∀ k : ℕ, |deriv (Fn τ) (xs τ k)| = (1 / ((k : ℝ) + 1)) ^ (2 / (3 - 2 * τ)) := by
    intro k
    rw [dFn_at τ hτ1, abs_neg, abs_of_pos (by have := stp_pos τ k; positivity)]
    unfold stp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  obtain ⟨B2, hB20, hB2⟩ := iter_Wt_bound 1
  obtain ⟨B3, hB30, hB3⟩ := iter_Wt_bound 2
  refine ⟨Fn τ, ?_, Fn_bdd τ hτ0 hτ1, ⟨B2, ?_⟩, ⟨Real.toNNReal B3, ?_⟩, xs τ, stp τ, fun _ => 1,
    by simp [xs], rfl, ?_, hgrad, ?_⟩
  · exact_mod_cast contDiff_infty.1 hsm 2
  · intro y
    obtain ⟨N, e2, _⟩ := dd_eq τ hτ0 hτ1 y
    rw [e2]
    apply Sm_bound τ hτ1 _ B2 hB20 (fun y hy => iter_Wt_zero 1 y hy) hB2
    intro k
    have pk := stp_pos τ k
    have : stp τ k ^ 3 / stp τ k / stp τ k = stp τ k := by field_simp
    rw [this, abs_of_pos pk]
    exact stp_le_one τ hτ1 k
  · have hd : Differentiable ℝ (deriv (deriv (Fn τ))) := by
      have := ContDiff.iterate_deriv 2 hsm
      exact this.differentiable (by simp)
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro y
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hB30]
    obtain ⟨N, _, e3⟩ := dd_eq τ hτ0 hτ1 y
    rw [e3]
    apply Sm_bound τ hτ1 _ B3 hB30 (fun y hy => iter_Wt_zero 2 y hy) hB3
    intro k
    have pk := stp_pos τ k
    have : stp τ k ^ 3 / stp τ k / stp τ k / stp τ k = 1 := by field_simp
    rw [this, abs_one]
  · intro γ₁ γ₂ η₁ η₂ h1 h2 h3 h4 h5
    have hr : ∀ k, rho (Fn τ) 1 (xs τ k) (stp τ k) = 3 / 2 := rho_eq τ hτ1
    refine ⟨⟨h1, h2, h3, h4, h5, by norm_num, fun k s' => model_min τ hτ1 k s', ?_, ?_⟩, ?_⟩
    · intro k
      simp only
      rw [hr k, if_pos (by linarith), xs_succ]
    · intro k
      simp only
      rw [hr k]
      refine ⟨fun _ => ⟨by norm_num, le_rfl⟩, fun h => ?_, fun h => ?_⟩
      · exfalso; linarith [h.2]
      · exfalso; linarith
    · intro k
      simp only
      rw [hr k]; linarith
  · intro ε hε _ k hk
    rw [hgrad k] at hk
    set a : ℝ := (1 / ((k : ℝ) + 1)) ^ (2 / (3 - 2 * τ)) with ha
    have hapos : 0 < a := by positivity
    have hp : 0 < 3 / 2 - τ := by linarith
    have hap : a ^ (3 / 2 - τ) = 1 / ((k : ℝ) + 1) := by
      rw [ha, ← Real.rpow_mul (by positivity)]
      have : 2 / (3 - 2 * τ) * (3 / 2 - τ) = 1 := by
        have hne : (3 : ℝ) - 2 * τ ≠ 0 := by linarith
        rw [div_mul_eq_mul_div, div_eq_one_iff_eq hne]
        ring
      rw [this, Real.rpow_one]
    have h1 : ε ^ (-(3 / 2 - τ)) ≤ (k : ℝ) + 1 := by
      rw [Real.rpow_neg hε.le]
      have h2 : a ^ (3 / 2 - τ) ≤ ε ^ (3 / 2 - τ) := Real.rpow_le_rpow hapos.le hk hp.le
      rw [hap] at h2
      have h3 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      calc (ε ^ (3 / 2 - τ))⁻¹ ≤ (1 / ((k : ℝ) + 1))⁻¹ := inv_anti₀ h3 h2
        _ = (k : ℝ) + 1 := by rw [one_div, inv_inv]
    exact (Nat.floor_le (by positivity)).trans h1

end SlowArcAux

open SlowConvergence.ARC in
theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
      (∃ M : ℝ, ∀ y, |deriv (deriv f) y| ≤ M) ∧
      (∃ L : NNReal, LipschitzWith L (deriv (deriv f))) ∧
      ∃ x s σ : ℕ → ℝ, x 0 = 0 ∧ σ 0 = 1 ∧
        (∀ γ₁ γ₂ η₁ η₂ : ℝ, 1 < γ₁ → γ₁ ≤ γ₂ → 0 < η₁ → η₁ ≤ η₂ → η₂ < 1 →
          IsARCRun f γ₁ γ₂ η₁ η₂ x s σ ∧ ∀ k, η₂ < rho f (σ k) (x k) (s k)) ∧
        (∀ k : ℕ, |deriv f (x k)| = (1 / ((k : ℝ) + 1)) ^ (2 / (3 - 2 * τ))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, |deriv f (x k)| ≤ ε →
          (⌊ε ^ (-(3 / 2 - τ))⌋₊ : ℝ) ≤ k + 1) := by
  exact SlowArcAux.main τ hτ0 hτ1
