-- Prove2me | solution 1 for SaglamGV.gammaKS_pos_and_lower
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T14:50:49.725268+00:00
-- url     : https://prove2.me/submissions/89c2e0c9-97ef-4c2a-8f41-75d64feaf0a2

import Definitions.Def_SaglamGV_Analytic
set_option autoImplicit false
open Set Filter SaglamGV
open scoped Topology

private lemma gamma_log (x : ℝ) : gammaKS x =
    (-(x / 2) * Real.log x - 2 * (1 - x) * Real.log (1 - x) - Real.log 2 +
      (1 - 3 * x / 2) * Real.log (2 - 3 * x)) / Real.log 2 := by
  unfold gammaKS Real.logb
  field_simp

private lemma gamma_cont : Continuous gammaKS := by
  have heq : gammaKS = fun x : ℝ ↦
      (Real.negMulLog x / 2 + 2 * Real.negMulLog (1 - x) - Real.log 2 -
        Real.negMulLog (2 - 3 * x) / 2) / Real.log 2 := by
    funext x
    rw [gamma_log]
    simp only [Real.negMulLog]
    ring
  rw [heq]
  fun_prop

private lemma gamma_deriv (x : ℝ) (hx : 0 < x) (hx2 : x < 2 / 3) :
    HasDerivAt gammaKS
      ((-Real.log x / 2 + 2 * Real.log (1 - x) - 3 / 2 * Real.log (2 - 3 * x)) /
        Real.log 2) x := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 2 - 3 * x := by linarith
  have ha := Real.hasDerivAt_log hx.ne'
  have hb := ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log h1.ne'
  have hc := ((hasDerivAt_const x 2).sub ((hasDerivAt_id x).const_mul 3)).log h2.ne'
  have h := (((((hasDerivAt_id x).div_const 2).neg.mul ha).sub
    (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).const_mul 2 |>.mul hb)).sub
    (hasDerivAt_const x (Real.log 2))).add
    (((hasDerivAt_const x 1).sub (((hasDerivAt_id x).const_mul 3).div_const 2)).mul hc)
  have hd := h.div_const (Real.log 2)
  convert! hd.congr_of_eventuallyEq (Filter.Eventually.of_forall gamma_log) using 1
  dsimp
  field_simp [hx.ne', h1.ne', h2.ne', (show 2 - x * 3 ≠ 0 by linarith)]
  ring

private lemma gamma_second (x : ℝ) (hx : 0 < x) (hx2 : x < 2 / 3) :
    deriv (deriv gammaKS) x =
      (3 * x - 1) / (x * (1 - x) * (2 - 3 * x) * Real.log 2) := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 2 - 3 * x := by linarith
  have ha := Real.hasDerivAt_log hx.ne'
  have hb := ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log h1.ne'
  have hc := ((hasDerivAt_const x 2).sub ((hasDerivAt_id x).const_mul 3)).log h2.ne'
  have hd := ((ha.neg.div_const 2).add (hb.const_mul 2) |>.sub (hc.const_mul (3 / 2))).div_const
    (Real.log 2)
  have heq : deriv gammaKS =ᶠ[𝓝 x] fun y : ℝ ↦
      (-Real.log y / 2 + 2 * Real.log (1 - y) - 3 / 2 * Real.log (2 - 3 * y)) /
        Real.log 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo 0 (2 / 3 : ℝ) from ⟨hx, hx2⟩)] with y hy
    exact (gamma_deriv y hy.1 hy.2).deriv
  rw [(hd.congr_of_eventuallyEq heq).deriv]
  dsimp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
  field_simp [hx.ne', h1.ne', h2.ne', (show 2 - x * 3 ≠ 0 by linarith)]
  ring

private lemma gamma_endpoints : gammaKS 0 = 0 ∧ gammaKS (1 / 2) = 0 ∧
    deriv gammaKS (1 / 2) = 0 := by
  have hl : Real.log (1 / 2) = -Real.log 2 := by simp [one_div, Real.log_inv]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [gammaKS]
  · rw [gamma_log]
    norm_num [hl]
  · rw [(gamma_deriv (1 / 2) (by norm_num) (by norm_num)).deriv]
    norm_num [hl]
    ring

private lemma gamma_positive : ∀ x : ℝ, 0 < x → x < 1 / 2 → 0 < gammaKS x := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcv : StrictConvexOn ℝ (Icc (1 / 3) (1 / 2)) gammaKS := by
    apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) gamma_cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    change 0 < deriv (deriv gammaKS) x
    rw [gamma_second x (by linarith [hx.1]) (by linarith [hx.2])]
    have hxp : 0 < x := by linarith [hx.1]
    have h1 : 0 < 1 - x := by linarith [hx.2]
    have h2 : 0 < 2 - 3 * x := by linarith [hx.2]
    exact div_pos (by linarith [hx.1]) (by positivity)
  have hright (x : ℝ) (hx : 1 / 3 ≤ x) (hx2 : x < 1 / 2) : 0 < gammaKS x := by
    have h := hcv.slope_lt_deriv ⟨hx, hx2.le⟩ (by constructor <;> norm_num) hx2
      (gamma_deriv (1 / 2) (by norm_num) (by norm_num)).differentiableAt
    rw [slope_def_field, gamma_endpoints.2.1, gamma_endpoints.2.2] at h
    have h' := (div_lt_iff₀ (show 0 < 1 / 2 - x by linarith)).mp h
    linarith
  have hcc : StrictConcaveOn ℝ (Icc 0 (1 / 3)) gammaKS := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) gamma_cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    change deriv (deriv gammaKS) x < 0
    rw [gamma_second x hx.1 (by linarith [hx.2])]
    have hxp : 0 < x := by linarith [hx.1]
    have h1 : 0 < 1 - x := by linarith [hx.2]
    have h2 : 0 < 2 - 3 * x := by linarith [hx.2]
    exact div_neg_of_neg_of_pos (by linarith [hx.2]) (by positivity)
  intro x hx hx2
  by_cases hx3 : 1 / 3 ≤ x
  · exact hright x hx3 hx2
  · have hconc := hcc.2
    have h := hconc (show (0 : ℝ) ∈ Icc 0 (1 / 3) by constructor <;> norm_num)
      (show (1 / 3 : ℝ) ∈ Icc 0 (1 / 3) by constructor <;> norm_num)
      (by norm_num : (0 : ℝ) ≠ 1 / 3)
      (a := 1 - 3 * x) (b := 3 * x) (by linarith) (by linarith) (by ring)
    simp only [smul_eq_mul, gamma_endpoints.1, mul_zero, zero_add] at h
    rw [show 3 * x * (1 / 3 : ℝ) = x by ring] at h
    have hp := hright (1 / 3) (by rfl) (by norm_num)
    nlinarith

private lemma gamma_remainder : ∃ C δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < x → x < δ →
    |gammaKS x - x / 2 * Real.logb 2 (1 / x)| ≤ C * x := by
  let R := fun x : ℝ ↦
    (-2 * (1 - x) * Real.log (1 - x) - Real.log 2 +
      (1 - 3 * x / 2) * Real.log (2 - 3 * x)) / Real.log 2
  have heq (x : ℝ) : gammaKS x - x / 2 * Real.logb 2 (1 / x) = R x := by
    rw [gamma_log]
    simp only [Real.logb, one_div, Real.log_inv, R]
    ring
  have hR0 : R 0 = 0 := by dsimp [R]; norm_num
  have hd : DifferentiableAt ℝ R 0 := by
    dsimp [R]
    fun_prop (disch := norm_num)
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hd.hasDerivAt.isBigO_sub
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨C, δ, hδ, ?_⟩
  intro x hx hxδ
  have h := hb (show dist x (0 : ℝ) < δ by simpa [Real.dist_eq, abs_of_pos hx] using hxδ)
  rw [heq]
  simpa only [hR0, sub_zero, Real.norm_eq_abs, abs_of_pos hx] using h


private lemma gamma_uniform (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → x ≤ 1 / 2 - η →
      c * x * Real.logb 2 (1 / x) ≤ gammaKS x := by
  obtain ⟨C, δ, hδ, herror⟩ := gamma_remainder
  have htend : Tendsto (fun x : ℝ ↦ Real.logb 2 (1 / x)) (𝓝[>] 0) atTop := by
    simpa only [Function.comp_def, one_div, Real.logb_inv] using
      (tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (b := 2) (by norm_num)))
  obtain ⟨δ₁, hδ₁, hlog⟩ := Metric.mem_nhdsWithin_iff.mp
    (htend.eventually (eventually_ge_atTop (4 * max C 0 + 1)))
  let a := min δ δ₁ / 2
  have ha : 0 < a := by dsimp [a]; exact div_pos (lt_min hδ hδ₁) (by norm_num)
  have haδ : a < δ := by
    have := min_le_left δ δ₁
    dsimp [a]
    linarith
  have haδ₁ : a < δ₁ := by
    have := min_le_right δ δ₁
    dsimp [a]
    linarith
  have hL (x : ℝ) (hx : 0 < x) (hx1 : x < 1) : 0 < Real.logb 2 (1 / x) :=
    Real.logb_pos (by norm_num) ((one_lt_div hx).mpr hx1)
  let F := fun x : ℝ ↦ gammaKS x / (x * Real.logb 2 (1 / x))
  have hcont : ContinuousOn F (Icc a (1 / 2 - η)) := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    have hx1 : x < 1 := by linarith [hx.2]
    have hLx := hL x hx0 hx1
    have hden : x * Real.logb 2 (1 / x) ≠ 0 := (mul_pos hx0 hLx).ne'
    apply ContinuousAt.continuousWithinAt
    dsimp [F]
    exact gamma_cont.continuousAt.div
      (continuousAt_id.mul ((continuousAt_const.div continuousAt_id hx0.ne').logb
        (div_ne_zero one_ne_zero hx0.ne'))) hden
  have hpos (x : ℝ) (hx : x ∈ Icc a (1 / 2 - η)) : 0 < F x := by
    have hx0 : 0 < x := ha.trans_le hx.1
    have hx2 : x < 1 / 2 := by linarith [hx.2]
    exact div_pos (gamma_positive x hx0 hx2) (mul_pos hx0 (hL x hx0 (by linarith)))
  obtain ⟨k, hk, hcomp⟩ := isCompact_Icc.exists_forall_le' hcont hpos
  refine ⟨min (1 / 4) k, lt_min (by norm_num) hk, ?_⟩
  intro x hx hxη
  have hLx : 0 < Real.logb 2 (1 / x) := hL x hx (by linarith)
  by_cases hxa : x < a
  · have he := (abs_le.mp (herror x hx (hxa.trans haδ))).1
    have hlogx : 4 * max C 0 + 1 ≤ Real.logb 2 (1 / x) := by
      apply hlog
      exact ⟨show x ∈ Metric.ball (0 : ℝ) δ₁ from
        (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hx] using hxa.trans haδ₁), hx⟩
    have hCx : C * x ≤ x * Real.logb 2 (1 / x) / 4 := by
      have hCb : C ≤ max C 0 := le_max_left _ _
      nlinarith [mul_nonneg hx.le (show 0 ≤ Real.logb 2 (1 / x) - 4 * C by linarith)]
    have hbase : (1 / 4 : ℝ) * x * Real.logb 2 (1 / x) ≤ gammaKS x := by nlinarith
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left (1 / 4 : ℝ) k) hx.le) hLx.le).trans hbase
  · have hfar := (le_div_iff₀ (mul_pos hx hLx)).mp (hcomp x ⟨by linarith, hxη⟩)
    have hmin := mul_le_mul_of_nonneg_right
      (min_le_right (1 / 4 : ℝ) k) (mul_pos hx hLx).le
    simpa only [mul_assoc] using hmin.trans hfar

theorem solution :
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 → 0 < gammaKS ρ) ∧
      (∃ C δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
        |gammaKS ρ - ρ / 2 * Real.logb 2 (1 / ρ)| ≤ C * ρ) ∧
      (∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 - η →
        c * ρ * Real.logb 2 (1 / ρ) ≤ gammaKS ρ) := by
  exact ⟨gamma_positive, gamma_remainder, gamma_uniform⟩
