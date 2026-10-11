-- Prove2me | solution 1 for ZetaEM.riemannZeta_eq_euler_maclaurin_nu_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T19:21:41.017962+00:00
-- url     : https://prove2.me/submissions/efbf5a70-9326-493d-852e-b699109a8936

import Mathlib
import Definitions.Def_SWPort_000

/-!
# Euler–Maclaurin for ζ(s) with ν = 1 (EM3 child of ac5b0112)

Route: `SWPort.Z.Zeta23_Zeta0EqZeta` (platform definition bundle `Def_SWPort_000`) gives the first-order
Euler–Maclaurin form `ζ(s) = Σ_{n ≤ N} n^{-s} - N^{1-s}/(1-s) - N^{-s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 - x) x^{-s-1} dx`
for `0 < Re s`, `s ≠ 1`. With `P_k(x) = B_k({x})` (right derivative `k P_{k-1}`, continuous for `k ≥ 2`),
the function `F(x) = P_2(x)/2 · x^{-(s+1)} + (s+1)/6 · P_3(x) x^{-s-2}` has right derivative
`P_1(x) x^{-(s+1)} - (s+1)(s+2)/6 · P_3(x) x^{-s-3}` at every `x > 0`; FTC on `[N, M]` (natural `M`, where
`F(M) = M^{-(s+1)}/12`) and `M → ∞` give the remainder integral in the `B_3` form.
-/

set_option autoImplicit false

namespace ZetaEM3Aux

open Complex MeasureTheory Set Filter Topology

/-- Right derivative of `x ↦ B_k({x})`. -/
theorem hasDerivWithinAt_bernoulliFun_fract (k : ℕ) (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => bernoulliFun k (Int.fract y))
      ((k : ℝ) * bernoulliFun (k - 1) (Int.fract x)) (Ici x) x := by
  have h1 : HasDerivAt (fun y : ℝ => bernoulliFun k (y - ((⌊x⌋ : ℤ) : ℝ)))
      ((k : ℝ) * bernoulliFun (k - 1) (Int.fract x)) x := by
    exact HasDerivAt.comp_sub_const x ((⌊x⌋ : ℤ) : ℝ)
      (hasDerivAt_bernoulliFun k (x - ((⌊x⌋ : ℤ) : ℝ)))
  have h2 : (fun y : ℝ => bernoulliFun k (Int.fract y)) =ᶠ[𝓝[≥] x]
      (fun y : ℝ => bernoulliFun k (y - ((⌊x⌋ : ℤ) : ℝ))) := by
    filter_upwards [Ico_mem_nhdsGE (Int.lt_floor_add_one x)] with y hy
    have hfl : ⌊y⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      exact ⟨(Int.floor_le x).trans hy.1, hy.2⟩
    show bernoulliFun k (y - ((⌊y⌋ : ℤ) : ℝ)) = _
    rw [hfl]
  exact h1.hasDerivWithinAt.congr_of_eventuallyEq h2 rfl

/-- `x ↦ B_k({x})` is continuous for `k ≠ 1`. -/
theorem continuous_bernoulliFun_fract {k : ℕ} (hk : k ≠ 1) :
    Continuous (fun y : ℝ => bernoulliFun k (Int.fract y)) :=
  (continuous_bernoulliFun k).continuousOn.comp_fract'' (bernoulliFun_endpoints_eq_of_ne_one hk).symm

theorem exists_bound_bernoulliFun_fract (k : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ, ‖bernoulliFun k (Int.fract y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliFun k).continuousOn
  exact ⟨C, fun y => hC _ ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩⟩

theorem integrableOn_B3 {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)) (Ioi a) := by
  obtain ⟨C, hC⟩ := exists_bound_bernoulliFun_fract 3
  refine Integrable.bdd_mul (c := C) ?_ ?_ ?_
  · refine integrableOn_Ioi_cpow_of_lt ?_ ha
    simp only [sub_re, neg_re, re_ofNat]
    linarith
  · exact (continuous_ofReal.comp (continuous_bernoulliFun_fract (k := 3) (by norm_num))).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by simpa only [Complex.norm_real] using hC x)

/-- The antiderivative. -/
theorem hasDerivWithinAt_F {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt
      (fun y : ℝ => (bernoulliFun 2 (Int.fract y) : ℂ) / 2 * (y : ℂ) ^ (-(s + 1))
        + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract y) : ℂ) * (y : ℂ) ^ (-s - 2)))
      (-(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)))
      (Ici x) x := by
  have hr1 : -(s + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [neg_re, add_re, one_re, zero_re] at this
    linarith
  have hr2 : -s - 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, neg_re, re_ofNat, zero_re] at this
    linarith
  have hB2 := (hasDerivWithinAt_bernoulliFun_fract 2 x).ofReal_comp
  have hB3 := (hasDerivWithinAt_bernoulliFun_fract 3 x).ofReal_comp
  have hP1 := (hasDerivAt_ofReal_cpow_const hx.ne' hr1).hasDerivWithinAt (s := Ici x)
  have hP2 := (hasDerivAt_ofReal_cpow_const hx.ne' hr2).hasDerivWithinAt (s := Ici x)
  have hF := ((hB2.div_const 2).mul hP1).add ((hB3.mul hP2).const_mul ((s + 1) / 6))
  refine hF.congr_deriv ?_
  have e1 : -(s + 1) - 1 = -s - 2 := by ring
  have e2 : -s - 2 - 1 = -s - 3 := by ring
  rw [e1, e2]
  norm_num [bernoulliFun_one]
  rw [show Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) from rfl]
  push_cast
  ring

/-- Continuity of the antiderivative on `[a, b]`, `0 < a`. -/
theorem continuousOn_F {s : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun y : ℝ => (bernoulliFun 2 (Int.fract y) : ℂ) / 2 * (y : ℂ) ^ (-(s + 1))
        + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract y) : ℂ) * (y : ℂ) ^ (-s - 2))) (Icc a b) := by
  have hc2 := continuous_ofReal.comp (continuous_bernoulliFun_fract (k := 2) (by norm_num))
  have hc3 := continuous_ofReal.comp (continuous_bernoulliFun_fract (k := 3) (by norm_num))
  have hp : ∀ c : ℂ, ContinuousOn (fun y : ℝ => (y : ℂ) ^ c) (Icc a b) := fun c y hy =>
    (continuousAt_ofReal_cpow_const y c (Or.inr (ha.trans_le hy.1).ne')).continuousWithinAt
  exact ((hc2.continuousOn.div_const 2).mul (hp _)).add
    (continuousOn_const.mul (hc3.continuousOn.mul (hp _)))

/-- The integrand `g`: the first-order remainder integrand (negated) minus the `B_3` remainder. -/
theorem integrableOn_g {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => -(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)))
      (Ioi (N : ℝ)) := by
  have h1 := SWPort.Z.integrableOn_of_Zeta0_fun_p1 hN hs
  have h3 := integrableOn_B3 (a := (N : ℝ)) (by exact_mod_cast hN) hs
  have := h1.neg.sub (h3.const_mul ((s + 1) * (s + 2) / 6))
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.neg_apply, Pi.sub_apply, neg_mul]

/-- Value of the antiderivative at a natural number. -/
theorem F_nat {s : ℂ} (n : ℕ) :
    (bernoulliFun 2 (Int.fract (n : ℝ)) : ℂ) / 2 * ((n : ℝ) : ℂ) ^ (-(s + 1))
        + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract (n : ℝ)) : ℂ) * ((n : ℝ) : ℂ) ^ (-s - 2))
      = (n : ℂ) ^ (-(s + 1)) / 12 := by
  have h3 : bernoulliFun 3 0 = 0 := by
    rw [bernoulliFun_eval_zero, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_three]
    simp
  have h2 : bernoulliFun 2 0 = 1 / 6 := by
    rw [bernoulliFun_two]; norm_num
  rw [Int.fract_natCast, h2, h3, Complex.ofReal_natCast]
  push_cast
  ring

/-- FTC on `[N, b]`. -/
theorem integral_g_interval {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) {b : ℝ} (hb : (N : ℝ) ≤ b) :
    ∫ x in (N : ℝ)..b, (-(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)))
      = ((bernoulliFun 2 (Int.fract b) : ℂ) / 2 * (b : ℂ) ^ (-(s + 1))
          + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract b) : ℂ) * (b : ℂ) ^ (-s - 2)))
        - ((bernoulliFun 2 (Int.fract (N : ℝ)) : ℂ) / 2 * ((N : ℝ) : ℂ) ^ (-(s + 1))
          + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract (N : ℝ)) : ℂ) * ((N : ℝ) : ℂ) ^ (-s - 2))) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb (continuousOn_F hN') ?_ ?_
  · intro x hx
    exact (hasDerivWithinAt_F hs (hN'.trans hx.1)).mono Ioi_subset_Ici_self
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact (integrableOn_g hN hs).mono_set Ioc_subset_Ioi_self

/-- The improper integral of `g` over `(N, ∞)`. -/
theorem integral_Ioi_g {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in Ioi (N : ℝ), (-(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)))
      = -((N : ℂ) ^ (-(s + 1)) / 12) := by
  have h1 := intervalIntegral_tendsto_integral_Ioi (N : ℝ) (integrableOn_g hN hs)
    tendsto_natCast_atTop_atTop
  have hs1 : 0 < (s + 1).re := by simp only [add_re, one_re]; linarith
  have hlim : Tendsto (fun M : ℕ => (M : ℂ) ^ (-(s + 1)) / 12 - (N : ℂ) ^ (-(s + 1)) / 12) atTop
      (𝓝 (0 / 12 - (N : ℂ) ^ (-(s + 1)) / 12)) := by
    refine (Tendsto.div_const ?_ 12).sub_const _
    simp_rw [Complex.cpow_neg]
    exact Complex.cpow_inv_tendsto_p1 hs1
  have h2 : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ),
      (-(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3))))
      atTop (𝓝 (0 / 12 - (N : ℂ) ^ (-(s + 1)) / 12)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    rw [integral_g_interval hN hs (by exact_mod_cast hM), F_nat, F_nat]
  rw [tendsto_nhds_unique h1 h2]
  ring

/-- The remainder integral of `ζ₀` in third-order form. -/
theorem integral_Ioi_floor_eq {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in Ioi (N : ℝ), (((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
      = (N : ℂ) ^ (-(s + 1)) / 12
        - (s + 1) * (s + 2) / 6 *
          ∫ x in Ioi (N : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3) := by
  have h := integral_Ioi_g hN hs
  have hi1 := SWPort.Z.integrableOn_of_Zeta0_fun_p1 hN hs
  have hi3 := integrableOn_B3 (a := (N : ℝ)) (by exact_mod_cast hN) hs
  rw [integral_sub (hi1.neg.congr_fun (fun x _ => by simp only [Pi.neg_apply, neg_mul])
      measurableSet_Ioi) (hi3.const_mul _)] at h
  simp only [neg_mul, integral_neg, integral_const_mul] at h
  linear_combination -h

theorem sum_range_eq_sum_Icc (N : ℕ) {s : ℂ} (hs : s ≠ 0) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp only [Nat.cast_zero, Complex.zero_cpow hs, div_zero, zero_add]
  rw [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [one_div, Complex.cpow_neg]

end ZetaEM3Aux

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s)
      - (N : ℂ) ^ (-s) / 2 + s * (N : ℂ) ^ (-s - 1) / 12
      - s * (s + 1) * (s + 2) / 6 *
          ∫ x in Set.Ioi (N : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3) := by
  have hN0 : 0 < N := hN
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  rw [← SWPort.Z.Zeta23_Zeta0EqZeta hN0 hs hs1, SWPort.Z.riemannZeta0_apply,
    ZetaEM3Aux.integral_Ioi_floor_eq hN0 hs, ZetaEM3Aux.sum_range_eq_sum_Icc N hs0]
  have e : -(s + 1) = -s - 1 := by ring
  rw [e]
  ring

#print axioms solution
