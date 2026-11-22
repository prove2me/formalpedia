-- Prove2me | solution 1 for SchwartzDist.dense_setOf_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:42:47.961573+00:00
-- url     : https://prove2.me/submissions/2b3957e6-f4f7-43c8-bc6d-06f9efd8b515

import Mathlib

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

open scoped ContDiff

namespace Sol_SchwartzDist_dense_setOf_hasCompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed smooth cut-off: equal to `1` on the closed unit ball, supported in the ball of radius 2. -/
noncomputable def chi (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ContDiffBump (0 : E) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The cut-off as a Schwartz function (it has compact support). -/
noncomputable def chiS (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : 𝓢(E, ℝ) :=
  (chi E).hasCompactSupport.toSchwartzMap (chi E).contDiff

omit [FiniteDimensional ℝ E] in
lemma norm_iteratedFDeriv_const_one_le (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun _ : E => (1 : ℝ)) x‖ ≤ 1 := by
  cases i with
  | zero => simp
  | succ i => simp [iteratedFDeriv_succ_const]

/-- Uniform bound (in `R ≥ 1`) on the derivatives of `y ↦ χ(y/R) - 1`. -/
lemma norm_iteratedFDeriv_cut_le (R : ℝ) (hR : 1 ≤ R) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => chi E (R⁻¹ • y) - 1) x‖ ≤
      SchwartzMap.seminorm ℝ 0 i (chiS E) + 1 := by
  have h1 : ContDiff ℝ i (fun y : E => chi E (R⁻¹ • y)) :=
    (chi E).contDiff.comp (contDiff_const_smul _)
  have hsub : iteratedFDeriv ℝ i (fun y : E => chi E (R⁻¹ • y) - 1) x =
      iteratedFDeriv ℝ i (fun y : E => chi E (R⁻¹ • y)) x -
        iteratedFDeriv ℝ i (fun _ : E => (1 : ℝ)) x :=
    iteratedFDeriv_sub_apply (f := fun y : E => chi E (R⁻¹ • y)) (g := fun _ : E => (1 : ℝ))
      h1.contDiffAt contDiffAt_const
  rw [hsub]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_iteratedFDeriv_const_one_le i x))
  rw [iteratedFDeriv_comp_const_smul R⁻¹ (chi E).contDiff]
  simp only
  rw [norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ R)]
  have hRi : (R⁻¹) ^ i ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hR)
  have hS : ‖iteratedFDeriv ℝ i (chi E) (R⁻¹ • x)‖ ≤ SchwartzMap.seminorm ℝ 0 i (chiS E) :=
    (chiS E).norm_iteratedFDeriv_le_seminorm ℝ i (R⁻¹ • x)
  calc (R⁻¹) ^ i * ‖iteratedFDeriv ℝ i (chi E) (R⁻¹ • x)‖
      ≤ 1 * SchwartzMap.seminorm ℝ 0 i (chiS E) := by
        gcongr
    _ = SchwartzMap.seminorm ℝ 0 i (chiS E) := one_mul _

/-- Inside the ball of radius `R` the truncation error vanishes with all its derivatives. -/
lemma iteratedFDeriv_cut_smul_eq_zero (R : ℝ) (hR : 0 < R) (f : E → F) (m : ℕ) (x : E)
    (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ m (fun y => (chi E (R⁻¹ • y) - 1) • f y) x = 0 := by
  have hev : (fun y => (chi E (R⁻¹ • y) - 1) • f y) =ᶠ[𝓝 x] fun _ => (0 : F) := by
    have hball : Metric.ball (0 : E) R ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (by simpa using hx)
    filter_upwards [hball] with y hy
    have hy' : ‖y‖ < R := by simpa using hy
    have h1 : chi E (R⁻¹ • y) = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
        Real.norm_of_nonneg hR.le]
      show R⁻¹ * ‖y‖ ≤ 1
      rw [inv_mul_le_iff₀ hR, mul_one]
      exact hy'.le
    simp [h1]
  rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
  simp

/-- The key estimate: the `(k, m)` Schwartz quantity of the truncation error is `O(1/R)`. -/
lemma main_bound (f : 𝓢(E, F)) (k m : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : E,
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun y => (chi E (R⁻¹ • y) - 1) • f y) x‖ ≤ M / R := by
  refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      (SchwartzMap.seminorm ℝ 0 i (chiS E) + 1) * SchwartzMap.seminorm ℝ (k + 1) (m - i) f,
      by positivity, ?_⟩
  intro R hR x
  have hR0 : 0 < R := by linarith
  rcases lt_or_ge ‖x‖ R with hx | hx
  · rw [iteratedFDeriv_cut_smul_eq_zero R hR0 (f : E → F) m x hx, norm_zero, mul_zero]
    positivity
  · rw [le_div_iff₀ hR0]
    have hsm : ContDiff ℝ m (fun y : E => chi E (R⁻¹ • y) - 1) :=
      ((chi E).contDiff.comp (contDiff_const_smul _)).sub contDiff_const
    have hf : ContDiff ℝ m (f : E → F) := (f.smooth ⊤).of_le (by exact_mod_cast le_top)
    have hL := norm_iteratedFDeriv_smul_le hsm hf x (n := m) le_rfl
    set D := ‖iteratedFDeriv ℝ m (fun y => (chi E (R⁻¹ • y) - 1) • f y) x‖ with hD
    have hD0 : 0 ≤ D := norm_nonneg _
    calc ‖x‖ ^ k * D * R ≤ ‖x‖ ^ (k + 1) * D := by
          rw [pow_succ, mul_right_comm]
          gcongr
      _ ≤ ‖x‖ ^ (k + 1) * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => chi E (R⁻¹ • y) - 1) x‖ *
            ‖iteratedFDeriv ℝ (m - i) (f : E → F) x‖ := by
          gcongr
      _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => chi E (R⁻¹ • y) - 1) x‖ *
            (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (m - i) (f : E → F) x‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          gcongr
          · exact norm_iteratedFDeriv_cut_le R hR i x
          · exact f.le_seminorm ℝ (k + 1) (m - i) x

end Sol_SchwartzDist_dense_setOf_hasCompactSupport

open Sol_SchwartzDist_dense_setOf_hasCompactSupport in
theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := by
  intro f
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcs : ∀ n : ℕ, HasCompactSupport (fun x : E => chi E (((n : ℝ) + 1)⁻¹ • x) • f x) :=
    fun n => ((chi E).hasCompactSupport.comp_smul (inv_ne_zero (hpos n).ne')).smul_right
  have hsm : ∀ n : ℕ, ContDiff ℝ ∞ (fun x : E => chi E (((n : ℝ) + 1)⁻¹ • x) • f x) :=
    fun n => ((chi E).contDiff.comp (contDiff_const_smul _)).smul (f.smooth ⊤)
  let u : ℕ → 𝓢(E, F) := fun n => (hcs n).toSchwartzMap (hsm n)
  refine mem_closure_of_tendsto (f := u) (b := atTop) ?_ (Eventually.of_forall fun n => hcs n)
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds u f]
  rintro ⟨k, m⟩ ε hε
  obtain ⟨M, hM0, hM⟩ := main_bound f k m
  have hlim : Tendsto (fun n : ℕ => M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul M
  filter_upwards [hlim.eventually_lt_const hε] with n hn
  refine lt_of_le_of_lt ?_ hn
  show SchwartzMap.seminorm ℝ k m (u n - f) ≤ _
  rw [mul_one_div]
  apply SchwartzMap.seminorm_le_bound ℝ k m _ (by have := hpos n; positivity)
  intro x
  have hcoe : ((u n - f : 𝓢(E, F)) : E → F) =
      fun y => (chi E (((n : ℝ) + 1)⁻¹ • y) - 1) • f y := by
    ext y
    simp only [sub_apply, sub_smul, one_smul]
    rfl
  rw [hcoe]
  exact hM _ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) x
