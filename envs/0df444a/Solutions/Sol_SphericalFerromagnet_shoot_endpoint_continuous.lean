-- Prove2me | solution 1 for SphericalFerromagnet.shoot_endpoint_continuous
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-05T01:05:31.414554+00:00
-- url     : https://prove2.me/submissions/83744ea3-4139-4a9b-852e-d4f8d2aad3d7

import Mathlib
import Definitions.Def_spherical_ferromagnet_shooting_defs

section Series

/-!
# Entire power series `cos √z`, `sin √z / √z`, `(sin √z - √z)/ z^{3/2}`

We define three entire functions of `z : ℝ` by power series and prove they are `C^∞`
together with the identities `C (y^2) = cos y`, `y * S (y^2) = sin y`,
`y^3 * S1 (y^2) = sin y - y`.
-/

open Real Filter Topology
open scoped ContDiff Nat

namespace P241S

/-- A real power series with `|c n| ≤ 1 / n!` defines a smooth function, and its sum. -/
theorem series_contDiff_hasSum (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1 / (n ! : ℝ)) :
    ContDiff ℝ ∞ (fun z : ℝ => ∑' n, c n * z ^ n) ∧
      ∀ z : ℝ, HasSum (fun n => c n * z ^ n) (∑' n, c n * z ^ n) := by
  set p := FormalMultilinearSeries.ofScalars ℝ c with hp
  have hrad : p.radius = ⊤ := by
    apply p.radius_eq_top_of_summable_norm
    intro r
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (Real.summable_pow_div_factorial (r : ℝ))
    rw [hp, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
    calc |c n| * (r : ℝ) ^ n ≤ 1 / (n ! : ℝ) * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (hc n) (by positivity)
      _ = (r : ℝ) ^ n / n ! := by ring
  have hball : HasFPowerSeriesOnBall p.sum p 0 ⊤ := by
    have := p.hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
    rwa [hrad] at this
  have hfun : (fun z : ℝ => ∑' n, c n * z ^ n) = p.sum := by
    funext z
    simp only [FormalMultilinearSeries.sum, hp, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
  refine ⟨?_, fun z => ?_⟩
  · rw [hfun, contDiff_iff_contDiffAt]
    intro z
    exact (hball.analyticAt_of_mem (by simp)).contDiffAt
  · have h := hball.hasSum (y := z) (by simp)
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at h
    have e := congrFun hfun z
    rw [e]; exact h

/-- coefficients of `cos √z` -/
noncomputable def cC (n : ℕ) : ℝ := (-1) ^ n / ((2 * n) ! : ℝ)
/-- coefficients of `sin √z / √z` -/
noncomputable def cS (n : ℕ) : ℝ := (-1) ^ n / ((2 * n + 1) ! : ℝ)
/-- coefficients of `(sin √z - √z) / z^{3/2}` -/
noncomputable def cS1 (n : ℕ) : ℝ := (-1) ^ (n + 1) / ((2 * n + 3) ! : ℝ)

/-- `C z = cos √z` (entire). -/
noncomputable def C (z : ℝ) : ℝ := ∑' n, cC n * z ^ n
/-- `S z = sin √z / √z` (entire). -/
noncomputable def S (z : ℝ) : ℝ := ∑' n, cS n * z ^ n
/-- `S1 z = (sin √z - √z) / z^{3/2}` (entire). -/
noncomputable def S1 (z : ℝ) : ℝ := ∑' n, cS1 n * z ^ n

lemma abs_coef_le {k n : ℕ} (hk : n ≤ k) (e : ℕ) :
    |(-1 : ℝ) ^ e / ((k) ! : ℝ)| ≤ 1 / (n ! : ℝ) := by
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.factorial_le hk

lemma C_spec : ContDiff ℝ ∞ C ∧ ∀ z, HasSum (fun n => cC n * z ^ n) (C z) :=
  series_contDiff_hasSum cC (fun n => abs_coef_le (by omega) n)

lemma S_spec : ContDiff ℝ ∞ S ∧ ∀ z, HasSum (fun n => cS n * z ^ n) (S z) :=
  series_contDiff_hasSum cS (fun n => abs_coef_le (by omega) n)

lemma S1_spec : ContDiff ℝ ∞ S1 ∧ ∀ z, HasSum (fun n => cS1 n * z ^ n) (S1 z) :=
  series_contDiff_hasSum cS1 (fun n => abs_coef_le (by omega) (n + 1))

lemma contDiff_C : ContDiff ℝ ∞ C := C_spec.1
lemma contDiff_S : ContDiff ℝ ∞ S := S_spec.1
lemma contDiff_S1 : ContDiff ℝ ∞ S1 := S1_spec.1

lemma C_sq (y : ℝ) : C (y ^ 2) = Real.cos y := by
  have h := C_spec.2 (y ^ 2)
  have e : (fun n => cC n * (y ^ 2) ^ n) =
      (fun n => (-1) ^ n * y ^ (2 * n) / ((2 * n) ! : ℝ)) := by
    funext n; simp only [cC]; rw [← pow_mul]; ring
  rw [e] at h
  exact h.unique (Real.hasSum_cos y)

lemma S_sq (y : ℝ) : y * S (y ^ 2) = Real.sin y := by
  have h := (S_spec.2 (y ^ 2)).mul_left y
  have e : (fun n => y * (cS n * (y ^ 2) ^ n)) =
      (fun n => (-1) ^ n * y ^ (2 * n + 1) / ((2 * n + 1) ! : ℝ)) := by
    funext n; simp only [cS]; rw [← pow_mul, pow_succ]; ring
  rw [e] at h
  exact h.unique (Real.hasSum_sin y)

lemma S1_sq (y : ℝ) : y ^ 3 * S1 (y ^ 2) = Real.sin y - y := by
  have h := (S1_spec.2 (y ^ 2)).mul_left (y ^ 3)
  have h2 := Real.hasSum_sin y
  rw [← hasSum_nat_add_iff' 1] at h2
  simp only [Finset.range_one, Finset.sum_singleton] at h2
  have e : (fun n => y ^ 3 * (cS1 n * (y ^ 2) ^ n)) =
      (fun n => (-1) ^ (n + 1) * y ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1) ! : ℝ)) := by
    funext n; simp only [cS1]
    have e1 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
    rw [e1, ← pow_mul]
    have : y ^ (2 * n + 3) = y ^ 3 * y ^ (2 * n) := by rw [← pow_add]; ring_nf
    rw [this]; ring
  rw [e] at h
  have := h.unique h2
  rw [this]; simp

end P241S

end Series

section Nonlin

/-!
# The nonlinearity `N(r, V)` of the profile equation in the variable `r = 1 - cos θ`

With `h = sin θ · V(1 - cos θ)` the profile equation at `κ = 4` becomes
`(r²(2-r)² V')' = r(2-r) N(r, V)` with `N` below (an entire function of `(r, V)`).
-/

open Real Set
open scoped ContDiff

namespace P241S

/-- `q r = r (2 - r) = sin² θ` when `r = 1 - cos θ`. -/
def qq (r : ℝ) : ℝ := r * (2 - r)

/-- The nonlinearity. -/
noncomputable def N (r V : ℝ) : ℝ :=
  2 * V + 4 * V ^ 3 * S1 (4 * qq r * V ^ 2) + 4 * V * S (4 * qq r * V ^ 2) * (1 - 2 * qq r)
    - 4 * (1 - r) * C (4 * qq r * V ^ 2)

lemma contDiff_N : ContDiff ℝ ∞ (fun p : ℝ × ℝ => N p.1 p.2) := by
  unfold N qq
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 4 * (p.1 * (2 - p.1)) * p.2 ^ 2) := by fun_prop
  have hS1 := contDiff_S1.comp h1
  have hS := contDiff_S.comp h1
  have hC := contDiff_C.comp h1
  simp only [Function.comp_def] at hS1 hS hC
  fun_prop

lemma contDiff_N_comp {n : ℕ} {f g : ℝ → ℝ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => N (f x) (g x)) :=
  (contDiff_infty.1 contDiff_N n).comp (hf.prodMk hg)

lemma continuous_N : Continuous (fun p : ℝ × ℝ => N p.1 p.2) := contDiff_N.continuous

/-- Trigonometric form of `N` when `q r = s²` with `s ≠ 0`. -/
lemma N_trig {r s V : ℝ} (hs : s ≠ 0) (hq : qq r = s ^ 2) :
    N r V = 2 * V + (Real.sin (2 * s * V) - 2 * s * V) / (2 * s ^ 3)
      + 2 * (1 - 2 * s ^ 2) * Real.sin (2 * s * V) / s - 4 * (1 - r) * Real.cos (2 * s * V) := by
  have hz : 4 * qq r * V ^ 2 = (2 * s * V) ^ 2 := by rw [hq]; ring
  unfold N
  rw [hz, ← C_sq, hq]
  have h1 := S1_sq (2 * s * V)
  have h2 := S_sq (2 * s * V)
  rw [← h2]
  rw [← h2] at h1
  generalize S ((2 * s * V) ^ 2) = T at *
  generalize S1 ((2 * s * V) ^ 2) = T1 at *
  field_simp
  apply mul_left_cancel₀ (show (2 * s) ≠ 0 by positivity)
  linear_combination h1

/-- The key identity used for the ODE in `θ`: with `s = sin θ ≠ 0`, `r = 1 - cos θ`. -/
lemma N_theta {θ g : ℝ} (hs : Real.sin θ ≠ 0) :
    Real.sin θ * N (1 - Real.cos θ) g = 2 * Real.sin θ * g
      + Real.sin (2 * (Real.sin θ * g)) / (2 * Real.sin θ ^ 2) - g / Real.sin θ
      + 2 * Real.sin (2 * (Real.sin θ * g) - 2 * θ) := by
  have hq : qq (1 - Real.cos θ) = Real.sin θ ^ 2 := by
    unfold qq; nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [N_trig hs hq, Real.sin_sub, Real.sin_two_mul θ, Real.cos_two_mul θ]
  have e : 2 * (Real.sin θ * g) = 2 * Real.sin θ * g := by ring
  rw [e]
  have hc := Real.sin_sq_add_cos_sq θ
  field_simp
  linear_combination (-8 * Real.sin θ ^ 2 * Real.sin (Real.sin θ * 2 * g)) * hc

lemma abs_cos_sub_cos_le' (a b : ℝ) : |Real.cos a - Real.cos b| ≤ |a - b| := by
  have := Real.lipschitzWith_cos.dist_le_mul a b
  simpa [Real.dist_eq] using this

/-- Global Lipschitz bound of `N r ·` away from the pole. -/
lemma N_lip_global {r ε x y : ℝ} (hε : 0 < ε) (hq : ε ≤ qq r) (hq1 : qq r ≤ 1)
    (hr : |1 - r| ≤ 1) : |N r x - N r y| ≤ (14 + 2 / ε) * |x - y| := by
  have hq0 : 0 < qq r := lt_of_lt_of_le hε hq
  set s := Real.sqrt (qq r) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hq0
  have hs2 : qq r = s ^ 2 := (Real.sq_sqrt hq0.le).symm
  have hs1 : s ≤ 1 := by
    rw [hsdef]; calc Real.sqrt (qq r) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hq1
      _ = 1 := Real.sqrt_one
  set a := 2 * s * x
  set b := 2 * s * y
  have hab : |a - b| = 2 * s * |x - y| := by
    simp only [a, b]; rw [show 2 * s * x - 2 * s * y = (2 * s) * (x - y) by ring, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * s)]
  have e : N r x - N r y = 2 * (x - y) + ((Real.sin a - Real.sin b) - (a - b)) / (2 * s ^ 3)
      + 2 * (1 - 2 * s ^ 2) * (Real.sin a - Real.sin b) / s
      - 4 * (1 - r) * (Real.cos a - Real.cos b) := by
    rw [N_trig hs.ne' hs2, N_trig hs.ne' hs2]; ring
  have hsin := Real.abs_sin_sub_sin_le a b
  have hcos := abs_cos_sub_cos_le' a b
  have t1 : |2 * (x - y)| = 2 * |x - y| := by rw [abs_mul]; norm_num
  have t2 : |((Real.sin a - Real.sin b) - (a - b)) / (2 * s ^ 3)| ≤ 2 / ε * |x - y| := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * s ^ 3)]
    rw [div_le_iff₀ (by positivity)]
    calc |Real.sin a - Real.sin b - (a - b)| ≤ |Real.sin a - Real.sin b| + |a - b| :=
          abs_sub _ _
      _ ≤ 2 * (2 * s * |x - y|) := by linarith
      _ ≤ 2 / ε * |x - y| * (2 * s ^ 3) := by
          have : 2 * (2 * s * |x - y|) * ε ≤ 2 / ε * |x - y| * (2 * s ^ 3) * ε := by
            rw [show 2 / ε * |x - y| * (2 * s ^ 3) * ε = 4 * s * |x - y| * s ^ 2 by
              field_simp; ring]
            rw [← hs2]
            have := abs_nonneg (x - y)
            nlinarith [mul_nonneg (mul_nonneg hs.le this) (sub_nonneg.2 hq)]
          exact le_of_mul_le_mul_right this hε
  have t3 : |2 * (1 - 2 * s ^ 2) * (Real.sin a - Real.sin b) / s| ≤ 4 * |x - y| := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs, abs_mul, abs_mul]
    have h12 : |1 - 2 * s ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have := abs_nonneg (Real.sin a - Real.sin b)
    calc |(2:ℝ)| * |1 - 2 * s ^ 2| * |Real.sin a - Real.sin b|
        ≤ 2 * 1 * |a - b| := by
          rw [abs_two]; gcongr
      _ = 4 * |x - y| * s := by rw [hab]; ring
  have t4 : |4 * (1 - r) * (Real.cos a - Real.cos b)| ≤ 8 * |x - y| := by
    rw [abs_mul, abs_mul]
    calc |(4:ℝ)| * |1 - r| * |Real.cos a - Real.cos b| ≤ 4 * 1 * |a - b| := by
          have := abs_nonneg (Real.cos a - Real.cos b)
          rw [show |(4:ℝ)| = 4 by norm_num]; gcongr
      _ = 8 * s * |x - y| := by rw [hab]; ring
      _ ≤ 8 * |x - y| := by
          have := abs_nonneg (x - y); nlinarith
  rw [e]
  calc _ ≤ |2 * (x - y)| + |((Real.sin a - Real.sin b) - (a - b)) / (2 * s ^ 3)|
        + |2 * (1 - 2 * s ^ 2) * (Real.sin a - Real.sin b) / s|
        + |4 * (1 - r) * (Real.cos a - Real.cos b)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ 2 * |x - y| + 2 / ε * |x - y| + 4 * |x - y| + 8 * |x - y| := by
        rw [t1]; gcongr
    _ = (14 + 2 / ε) * |x - y| := by ring

/-- Lipschitz bound of `N r ·` on a compact box. -/
lemma N_lip_compact : ∃ L : ℝ, 0 ≤ L ∧ ∀ r ∈ Icc (-1 : ℝ) 1, ∀ x ∈ Icc (-6 : ℝ) 6,
    ∀ y ∈ Icc (-6 : ℝ) 6, |N r x - N r y| ≤ L * |x - y| := by
  obtain ⟨K, hK⟩ := (contDiff_N.contDiffOn (s := Icc (-1 : ℝ) 1 ×ˢ Icc (-6 : ℝ) 6)).exists_lipschitzOnWith
    (by simp) ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  refine ⟨K, K.2, fun r hr x hx y hy => ?_⟩
  have := hK.dist_le_mul (r, x) ⟨hr, hx⟩ (r, y) ⟨hr, hy⟩
  simpa [Real.dist_eq, Prod.dist_eq] using this

/-- Bound of `N` on a compact box. -/
lemma N_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc (-1 : ℝ) 1, ∀ x ∈ Icc (-6 : ℝ) 6, |N r x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuous_N.continuousOn (s := Icc (-1 : ℝ) 1 ×ˢ Icc (-6 : ℝ) 6))
  refine ⟨max B 0, le_max_right _ _, fun r hr x hx => ?_⟩
  have := hB (r, x) ⟨hr, hx⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

end P241S

end Nonlin

section ParamInt

/-!
# Smoothness of parametric integrals over `[0,1]`
-/

open Real Set MeasureTheory
open scoped ContDiff

namespace P241S

theorem contDiff_integral01 (n : ℕ) :
    ∀ F : ℝ → ℝ → ℝ, ContDiff ℝ n (Function.uncurry F) →
      ContDiff ℝ n (fun ρ => ∫ τ in (0 : ℝ)..1, F ρ τ) := by
  induction n with
  | zero =>
    intro F hF
    rw [Nat.cast_zero, contDiff_zero] at *
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF
      continuous_const
  | succ n ih =>
    intro F hF
    set F' : ℝ → ℝ → ℝ := fun ρ τ => fderiv ℝ (Function.uncurry F) (ρ, τ) (1, 0) with hF'def
    have hF' : ContDiff ℝ n (Function.uncurry F') := by
      have h1 : ContDiff ℝ n (fderiv ℝ (Function.uncurry F)) :=
        hF.fderiv_right (by push_cast; exact le_rfl)
      have : Function.uncurry F' = fun p => fderiv ℝ (Function.uncurry F) p (1, 0) := by
        funext ⟨ρ, τ⟩; rfl
      rw [this]
      exact h1.clm_apply contDiff_const
    have hdiff : Differentiable ℝ (Function.uncurry F) :=
      hF.differentiable (by simp)
    have hderiv : ∀ ρ τ, HasDerivAt (fun ρ => F ρ τ) (F' ρ τ) ρ := by
      intro ρ τ
      have := (hdiff (ρ, τ)).hasFDerivAt.comp_hasDerivAt ρ
        ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ τ))
      exact this
    have hcontF' : Continuous (Function.uncurry F') := hF'.continuous
    have hcontF : Continuous (Function.uncurry F) := hF.continuous
    have hint : ∀ ρ0, HasDerivAt (fun ρ => ∫ τ in (0 : ℝ)..1, F ρ τ)
        (∫ τ in (0 : ℝ)..1, F' ρ0 τ) ρ0 := by
      intro ρ0
      obtain ⟨Cb, hCb⟩ := (isCompact_closedBall ρ0 1 |>.prod isCompact_Icc).exists_bound_of_continuousOn
        (hcontF'.continuousOn (s := Metric.closedBall ρ0 1 ×ˢ Icc (0 : ℝ) 1))
      have hcF : ∀ x, Continuous (F x) := fun x => hcontF.comp (Continuous.prodMk_right x)
      have hcF' : ∀ x, Continuous (F' x) := fun x => hcontF'.comp (Continuous.prodMk_right x)
      refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (bound := fun _ => Cb) (F' := F') (Metric.ball_mem_nhds ρ0 one_pos)
        (Filter.Eventually.of_forall fun x => (hcF x).aestronglyMeasurable)
        ((hcF ρ0).intervalIntegrable _ _) ((hcF' ρ0).aestronglyMeasurable) ?_
        intervalIntegrable_const ?_).2
      · refine Filter.Eventually.of_forall fun t ht x hx => ?_
        apply hCb (x, t)
        refine ⟨Metric.ball_subset_closedBall hx, ?_⟩
        rw [uIoc_of_le zero_le_one] at ht
        exact Ioc_subset_Icc_self ht
      · exact Filter.Eventually.of_forall fun t _ x _ => hderiv x t
    have hd : deriv (fun ρ => ∫ τ in (0 : ℝ)..1, F ρ τ) = fun ρ => ∫ τ in (0 : ℝ)..1, F' ρ τ := by
      funext ρ; exact (hint ρ).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun ρ => (hint ρ).differentiableAt, by simp, ?_⟩
    rw [hd]
    exact ih F' hF'

end P241S

end ParamInt

section Operator

/-!
# Cut-offs, the averaging operator `J`, and the Volterra operator `G`

The singular equation `(r²(2-r)² V')' = r(2-r) N(r,V)` with `V(0) = a` is rewritten as
`V(r) = a + ∫₀ʳ κ(ρ) J[N(·,V)](ρ) dρ`, `J f (ρ) = ∫₀¹ τ (2 - ρτ) f(ρτ) dτ`,
`κ(ρ) = (2-ρ)⁻²`. We insert cut-offs to obtain a globally Lipschitz problem on all of `ℝ`.
-/

open Real Set MeasureTheory
open scoped ContDiff

namespace P241S

/-- smooth cut-off: `1` on `[-ε, 1]`, `0` outside `(-2ε, 1+ε)`. -/
noncomputable def eta (ε σ : ℝ) : ℝ :=
  smoothTransition ((σ + 2 * ε) / ε) * smoothTransition ((1 + ε - σ) / ε)

/-- smooth version of `(2 - ρ)⁻²` (exact for `ρ ≤ 3/2`). -/
noncomputable def kap (ρ : ℝ) : ℝ := ((2 - ρ) ^ 2 + smoothTransition (ρ - 3 / 2))⁻¹

/-- continuous switch: `1` for `σ ≤ ε`, `0` for `σ ≥ 2ε`. -/
noncomputable def chi (ε σ : ℝ) : ℝ := max 0 (min 1 ((2 * ε - σ) / ε))

/-- clamp to `[-6, 6]`. -/
noncomputable def clampM (x : ℝ) : ℝ := max (-6) (min 6 x)

/-- modified nonlinearity (globally Lipschitz in `x`). -/
noncomputable def Nt (ε σ x : ℝ) : ℝ := N σ (chi ε σ * clampM x + (1 - chi ε σ) * x)

/-- averaging operator. -/
noncomputable def J (f : ℝ → ℝ) (ρ : ℝ) : ℝ := ∫ τ in (0 : ℝ)..1, τ * (2 - ρ * τ) * f (ρ * τ)

/-- the source term. -/
noncomputable def fv (ε : ℝ) (v : ℝ → ℝ) (σ : ℝ) : ℝ := eta ε σ * Nt ε σ (v σ)

/-- the Volterra operator. -/
noncomputable def G (ε a : ℝ) (v : ℝ → ℝ) (r : ℝ) : ℝ :=
  a + ∫ ρ in (0 : ℝ)..r, kap ρ * J (fv ε v) ρ

/-! ### cut-off lemmas -/

lemma contDiff_eta (ε : ℝ) : ContDiff ℝ ∞ (eta ε) := by
  unfold eta
  have h : ContDiff ℝ ∞ smoothTransition := smoothTransition.contDiff
  exact (h.comp (by fun_prop)).mul (h.comp (by fun_prop))

lemma eta_nonneg (ε σ : ℝ) : 0 ≤ eta ε σ :=
  mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _)

lemma eta_le_one (ε σ : ℝ) : eta ε σ ≤ 1 := by
  unfold eta
  calc _ ≤ 1 * 1 := mul_le_mul (smoothTransition.le_one _) (smoothTransition.le_one _)
        (smoothTransition.nonneg _) zero_le_one
    _ = 1 := by ring

lemma eta_eq_one {ε σ : ℝ} (hε : 0 < ε) (h1 : -ε ≤ σ) (h2 : σ ≤ 1) : eta ε σ = 1 := by
  unfold eta
  rw [smoothTransition.one_of_one_le, smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hε]; linarith
  · rw [le_div_iff₀ hε]; linarith

lemma eta_eq_zero_of_le {ε σ : ℝ} (hε : 0 < ε) (h : σ ≤ -2 * ε) : eta ε σ = 0 := by
  unfold eta
  rw [smoothTransition.zero_of_nonpos, zero_mul]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le

lemma eta_eq_zero_of_ge {ε σ : ℝ} (hε : 0 < ε) (h : 1 + ε ≤ σ) : eta ε σ = 0 := by
  unfold eta
  rw [smoothTransition.zero_of_nonpos (x := (1 + ε - σ) / ε), mul_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le

lemma kap_denom_pos (ρ : ℝ) : 0 < (2 - ρ) ^ 2 + smoothTransition (ρ - 3 / 2) := by
  rcases le_or_gt ρ (3 / 2) with h | h
  · have : 0 < (2 - ρ) ^ 2 := by nlinarith
    linarith [smoothTransition.nonneg (ρ - 3 / 2)]
  · have := smoothTransition.pos_of_pos (show 0 < ρ - 3 / 2 by linarith)
    nlinarith [sq_nonneg (2 - ρ)]

lemma contDiff_kap : ContDiff ℝ ∞ kap := by
  unfold kap
  have h : ContDiff ℝ ∞ smoothTransition := smoothTransition.contDiff
  exact ContDiff.inv (by fun_prop) (fun ρ => (kap_denom_pos ρ).ne')

lemma kap_eq {ρ : ℝ} (h : ρ ≤ 3 / 2) : kap ρ = ((2 - ρ) ^ 2)⁻¹ := by
  unfold kap
  rw [smoothTransition.zero_of_nonpos (by linarith), add_zero]

lemma kap_nonneg (ρ : ℝ) : 0 ≤ kap ρ := (inv_pos.2 (kap_denom_pos ρ)).le

lemma kap_le {ρ : ℝ} (h : ρ ≤ 3 / 2) : kap ρ ≤ 4 := by
  rw [kap_eq h]
  have : (1 / 4 : ℝ) ≤ (2 - ρ) ^ 2 := by nlinarith
  calc ((2 - ρ) ^ 2)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
    _ = 4 := by norm_num

lemma continuous_chi (ε : ℝ) : Continuous (chi ε) := by unfold chi; fun_prop

lemma chi_nonneg (ε σ : ℝ) : 0 ≤ chi ε σ := le_max_left _ _
lemma chi_le_one (ε σ : ℝ) : chi ε σ ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma chi_eq_one {ε σ : ℝ} (hε : 0 < ε) (h : σ ≤ ε) : chi ε σ = 1 := by
  unfold chi
  rw [min_eq_left, max_eq_right zero_le_one]
  rw [le_div_iff₀ hε]; linarith

lemma chi_eq_zero {ε σ : ℝ} (hε : 0 < ε) (h : 2 * ε ≤ σ) : chi ε σ = 0 := by
  unfold chi
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma continuous_clampM : Continuous clampM := by unfold clampM; fun_prop

lemma clampM_mem (x : ℝ) : clampM x ∈ Icc (-6 : ℝ) 6 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clampM_of_abs_le {x : ℝ} (h : |x| ≤ 6) : clampM x = x := by
  unfold clampM
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma abs_clampM_sub (x y : ℝ) : |clampM x - clampM y| ≤ |x - y| := by
  unfold clampM
  rw [max_comm (-6) (min 6 x), max_comm (-6) (min 6 y)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

lemma continuous_Nt (ε : ℝ) : Continuous (fun p : ℝ × ℝ => Nt ε p.1 p.2) := by
  unfold Nt
  have h1 := continuous_chi ε
  have h2 := continuous_clampM
  have : Continuous (fun p : ℝ × ℝ =>
      (p.1, chi ε p.1 * clampM p.2 + (1 - chi ε p.1) * p.2)) := by fun_prop
  exact continuous_N.comp this

lemma Nt_eq_of_abs_le {ε σ x : ℝ} (h : |x| ≤ 6) : Nt ε σ x = N σ x := by
  unfold Nt; rw [clampM_of_abs_le h]; ring_nf

lemma Nt_eq_of_ge {ε σ x : ℝ} (hε : 0 < ε) (h : 2 * ε ≤ σ) : Nt ε σ x = N σ x := by
  unfold Nt; rw [chi_eq_zero hε h]; ring_nf

/-- Uniform Lipschitz bound for the modified nonlinearity on the working interval. -/
lemma Nt_lip {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ σ ∈ Icc (-2 * ε) (1 + ε), ∀ x y : ℝ,
      |Nt ε σ x - Nt ε σ y| ≤ L * |x - y| := by
  obtain ⟨L1, hL1, hL1'⟩ := N_lip_compact
  refine ⟨max L1 (14 + 2 / ε), le_max_of_le_left hL1, fun σ hσ x y => ?_⟩
  rcases le_or_gt σ ε with h | h
  · unfold Nt
    rw [chi_eq_one hε h]
    simp only [one_mul, sub_self, zero_mul, add_zero]
    calc _ ≤ L1 * |clampM x - clampM y| :=
          hL1' σ ⟨by linarith [hσ.1], by linarith⟩ _ (clampM_mem x) _ (clampM_mem y)
      _ ≤ max L1 (14 + 2 / ε) * |x - y| :=
          mul_le_mul (le_max_left _ _) (abs_clampM_sub x y) (abs_nonneg _)
            (le_max_of_le_left hL1)
  · unfold Nt
    have hq : ε ≤ qq σ := by unfold qq; nlinarith [hσ.2]
    have hq1 : qq σ ≤ 1 := by unfold qq; nlinarith [sq_nonneg (σ - 1)]
    have hr : |1 - σ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hσ.2]
    refine (N_lip_global hε hq hq1 hr).trans ?_
    have hc0 := chi_nonneg ε σ
    have hc1 := chi_le_one ε σ
    have harg : |(chi ε σ * clampM x + (1 - chi ε σ) * x) - (chi ε σ * clampM y + (1 - chi ε σ) * y)|
        ≤ |x - y| := by
      rw [show (chi ε σ * clampM x + (1 - chi ε σ) * x) - (chi ε σ * clampM y + (1 - chi ε σ) * y)
        = chi ε σ * (clampM x - clampM y) + (1 - chi ε σ) * (x - y) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg (by linarith : 0 ≤ 1 - chi ε σ)]
      have := abs_clampM_sub x y
      nlinarith
    exact mul_le_mul (le_max_right _ _) harg (abs_nonneg _) (le_max_of_le_left hL1)

/-! ### continuity / derivative of the operators -/

lemma continuous_J {f : ℝ → ℝ} (hf : Continuous f) : Continuous (J f) := by
  unfold J
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun ρ τ => τ * (2 - ρ * τ) * f (ρ * τ)) (by fun_prop) continuous_const

lemma contDiff_J {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) : ContDiff ℝ n (J f) := by
  unfold J
  apply contDiff_integral01 n (fun ρ τ => τ * (2 - ρ * τ) * f (ρ * τ))
  have : ContDiff ℝ n (fun p : ℝ × ℝ => f (p.1 * p.2)) := hf.comp (by fun_prop)
  change ContDiff ℝ n (fun p : ℝ × ℝ => p.2 * (2 - p.1 * p.2) * f (p.1 * p.2))
  fun_prop

lemma continuous_fv {ε : ℝ} {v : ℝ → ℝ} (hv : Continuous v) : Continuous (fv ε v) := by
  unfold fv
  have := (continuous_Nt ε).comp (continuous_id.prodMk hv)
  exact (contDiff_eta ε).continuous.mul this

lemma continuous_kapJ {ε : ℝ} {v : ℝ → ℝ} (hv : Continuous v) :
    Continuous (fun ρ => kap ρ * J (fv ε v) ρ) :=
  contDiff_kap.continuous.mul (continuous_J (continuous_fv hv))

lemma hasDerivAt_G {ε a : ℝ} {v : ℝ → ℝ} (hv : Continuous v) (r : ℝ) :
    HasDerivAt (G ε a v) (kap r * J (fv ε v) r) r := by
  unfold G
  exact ((continuous_kapJ hv).integral_hasStrictDerivAt 0 r).hasDerivAt.const_add a

lemma continuous_G {ε a : ℝ} {v : ℝ → ℝ} (hv : Continuous v) : Continuous (G ε a v) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_G hv r).continuousAt

end P241S

end Operator

section Estimates

/-!
# Pointwise estimates for the Volterra operator `G`
-/

open Real Set MeasureTheory
open scoped ContDiff Nat

namespace P241S

/-- `|∫₀ʳ F| ≤ c |r|^{k+1}/(k+1)` if `|F ρ| ≤ c |ρ|^k` between `0` and `r`. -/
lemma int_pow_bound {F : ℝ → ℝ} (_hF : Continuous F) {c : ℝ} (k : ℕ) (r : ℝ)
    (h : ∀ ρ ∈ uIcc 0 r, |F ρ| ≤ c * |ρ| ^ k) :
    |∫ ρ in (0 : ℝ)..r, F ρ| ≤ c * |r| ^ (k + 1) / (k + 1) := by
  rcases le_total 0 r with hr | hr
  · have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (g := fun ρ => c * ρ ^ k) hr
      (Filter.Eventually.of_forall fun t ht => by
        have h1 := h t (by rw [uIcc_of_le hr]; exact Ioc_subset_Icc_self ht)
        rw [Real.norm_eq_abs]
        rwa [abs_of_nonneg ht.1.le] at h1)
      (by apply Continuous.intervalIntegrable; fun_prop)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_pow] at this
    rw [abs_of_nonneg hr]
    calc _ ≤ _ := this
      _ = c * r ^ (k + 1) / (k + 1) := by
        rw [zero_pow (Nat.succ_ne_zero k)]; ring
  · rw [intervalIntegral.integral_symm, abs_neg]
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (g := fun ρ => c * (-ρ) ^ k) hr
      (Filter.Eventually.of_forall fun t ht => by
        have h1 := h t (by rw [uIcc_of_ge hr]; exact Ioc_subset_Icc_self ht)
        rw [Real.norm_eq_abs]
        rwa [abs_of_nonpos ht.2] at h1)
      (by apply Continuous.intervalIntegrable; fun_prop)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_neg (fun x => x ^ k), integral_pow] at this
    rw [abs_of_nonpos hr]
    calc _ ≤ _ := this
      _ = c * (-r) ^ (k + 1) / (k + 1) := by
        rw [neg_zero, zero_pow (Nat.succ_ne_zero k)]; ring

/-- membership helper -/
lemma mem_Icc_of_uIcc {A B r ρ : ℝ} (hA : A ≤ 0) (hB : 0 ≤ B) (hr : r ∈ Icc A B)
    (hρ : ρ ∈ uIcc 0 r) : ρ ∈ Icc A B := by
  rcases le_total 0 r with h | h
  · rw [uIcc_of_le h] at hρ; exact ⟨by linarith [hρ.1], by linarith [hρ.2, hr.2]⟩
  · rw [uIcc_of_ge h] at hρ; exact ⟨by linarith [hρ.1, hr.1], by linarith [hρ.2]⟩

lemma mem_Icc_mul {A B ρ τ : ℝ} (hA : A ≤ 0) (hB : 0 ≤ B) (hρ : ρ ∈ Icc A B)
    (hτ : τ ∈ Icc (0 : ℝ) 1) : ρ * τ ∈ Icc A B := by
  constructor
  · rcases le_total 0 ρ with h | h
    · nlinarith [hτ.1]
    · nlinarith [hτ.2, hρ.1]
  · rcases le_total 0 ρ with h | h
    · nlinarith [hτ.2, hρ.2]
    · nlinarith [hτ.1]

/-- Bound on the `J`-integrand. -/
lemma J_bound {f : ℝ → ℝ} (_hf : Continuous f) {ρ : ℝ} (hρ1 : -1 / 2 ≤ ρ) (hρ2 : ρ ≤ 5 / 4)
    {M : ℝ} (hM : ∀ τ ∈ Icc (0 : ℝ) 1, |f (ρ * τ)| ≤ M) : |J f ρ| ≤ 3 * M := by
  unfold J
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 3 * M)
    (f := fun τ => τ * (2 - ρ * τ) * f (ρ * τ)) (fun τ hτ => by
      rw [uIoc_of_le zero_le_one] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hτ
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |τ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hτ'.1, hτ'.2]
      have h2 : |2 - ρ * τ| ≤ 3 := by
        rw [abs_le]; constructor <;> nlinarith [hτ'.1, hτ'.2]
      have h3 := hM τ hτ'
      calc |τ| * |2 - ρ * τ| * |f (ρ * τ)| ≤ 1 * 3 * M := by gcongr
        _ = 3 * M := by ring)
  simpa using this

variable {ε : ℝ}

/-- One step of the Picard-type estimate (with two slopes `a`, `b`). -/
lemma G_step (hε : 0 < ε) (hε' : ε ≤ 1 / 4) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ σ ∈ Icc (-2 * ε) (1 + ε), ∀ x y : ℝ, |Nt ε σ x - Nt ε σ y| ≤ L * |x - y|)
    {v w : ℝ → ℝ} (hv : Continuous v) (hw : Continuous w) {D : ℝ} (hD : 0 ≤ D) (k : ℕ)
    (hvw : ∀ σ ∈ Icc (-2 * ε) (1 + ε), |v σ - w σ| ≤ D * (12 * L * |σ|) ^ k / k !)
    (a b : ℝ) :
    ∀ r ∈ Icc (-2 * ε) (1 + ε),
      |G ε a v r - G ε b w r| ≤ |a - b| + D * (12 * L * |r|) ^ (k + 1) / (k + 1)! := by
  intro r hr
  have hA : -2 * ε ≤ 0 := by linarith
  have hB : 0 ≤ 1 + ε := by linarith
  have hcv := continuous_kapJ (ε := ε) hv
  have hcw := continuous_kapJ (ε := ε) hw
  have e : G ε a v r - G ε b w r = (a - b) +
      ∫ ρ in (0 : ℝ)..r, (kap ρ * J (fv ε v) ρ - kap ρ * J (fv ε w) ρ) := by
    unfold G
    rw [intervalIntegral.integral_sub (hcv.intervalIntegrable _ _) (hcw.intervalIntegrable _ _)]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
  have hcont : Continuous (fun ρ => kap ρ * J (fv ε v) ρ - kap ρ * J (fv ε w) ρ) := hcv.sub hcw
  have key := int_pow_bound hcont (c := D * (12 * L) ^ (k + 1) / k !) k r (fun ρ hρ => by
    have hρ' := mem_Icc_of_uIcc hA hB hr hρ
    rw [← mul_sub, abs_mul, abs_of_nonneg (kap_nonneg ρ)]
    have hJ : |J (fv ε v) ρ - J (fv ε w) ρ| ≤ 3 * (L * (D * (12 * L * |ρ|) ^ k / k !)) := by
      have hsub : J (fv ε v) ρ - J (fv ε w) ρ = J (fun σ => fv ε v σ - fv ε w σ) ρ := by
        unfold J
        rw [← intervalIntegral.integral_sub]
        · congr 1; funext τ; ring
        · apply Continuous.intervalIntegrable
          have := continuous_fv (ε := ε) hv; fun_prop
        · apply Continuous.intervalIntegrable
          have := continuous_fv (ε := ε) hw; fun_prop
      rw [hsub]
      apply J_bound ((continuous_fv hv).sub (continuous_fv hw))
        (by linarith [hρ'.1]) (by linarith [hρ'.2])
      intro τ hτ
      have hσ := mem_Icc_mul hA hB hρ' hτ
      show |eta ε (ρ * τ) * Nt ε (ρ * τ) (v (ρ * τ)) - eta ε (ρ * τ) * Nt ε (ρ * τ) (w (ρ * τ))| ≤ _
      rw [← mul_sub, abs_mul, abs_of_nonneg (eta_nonneg _ _)]
      have h1 := hLip _ hσ (v (ρ * τ)) (w (ρ * τ))
      have h2 := hvw _ hσ
      have h3 : |ρ * τ| ≤ |ρ| := by
        have hτ1 : |τ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
        rw [abs_mul]
        calc |ρ| * |τ| ≤ |ρ| * 1 := by gcongr
          _ = |ρ| := mul_one _
      have h4 : D * (12 * L * |ρ * τ|) ^ k / k ! ≤ D * (12 * L * |ρ|) ^ k / k ! := by
        gcongr
      calc eta ε (ρ * τ) * |Nt ε (ρ * τ) (v (ρ * τ)) - Nt ε (ρ * τ) (w (ρ * τ))|
          ≤ 1 * (L * |v (ρ * τ) - w (ρ * τ)|) :=
            mul_le_mul (eta_le_one _ _) h1 (abs_nonneg _) zero_le_one
        _ ≤ 1 * (L * (D * (12 * L * |ρ|) ^ k / k !)) := by gcongr; exact h2.trans h4
        _ = L * (D * (12 * L * |ρ|) ^ k / k !) := one_mul _
    calc kap ρ * |J (fv ε v) ρ - J (fv ε w) ρ| ≤ 4 * (3 * (L * (D * (12 * L * |ρ|) ^ k / k !))) :=
          mul_le_mul (kap_le (by linarith [hρ'.2])) hJ (abs_nonneg _) (by norm_num)
      _ = D * (12 * L) ^ (k + 1) / k ! * |ρ| ^ k := by rw [mul_pow, pow_succ]; ring)
  calc _ ≤ D * (12 * L) ^ (k + 1) / k ! * |r| ^ (k + 1) / (k + 1) := key
    _ = D * (12 * L * |r|) ^ (k + 1) / (k + 1)! := by
      rw [Nat.factorial_succ, mul_pow, mul_pow]; push_cast; field_simp; ring

/-- A priori bound: the operator preserves `|v - a| ≤ 1` on `[-2ε, 2ε]`. -/
lemma G_apriori (hε : 0 < ε) (hε' : ε ≤ 1 / 4) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ r ∈ Icc (-1 : ℝ) 1, ∀ x ∈ Icc (-6 : ℝ) 6, |N r x| ≤ B) (hεB : 24 * ε * B ≤ 1)
    {a : ℝ} (ha : a ∈ Icc (3 : ℝ) 5) {v : ℝ → ℝ} (hv : Continuous v)
    (hva : ∀ σ ∈ Icc (-2 * ε) (2 * ε), |v σ - a| ≤ 1) :
    ∀ r ∈ Icc (-2 * ε) (2 * ε), |G ε a v r - a| ≤ 1 := by
  intro r hr
  have hA : -2 * ε ≤ 0 := by linarith
  have hB' : 0 ≤ 2 * ε := by linarith
  have e : G ε a v r - a = ∫ ρ in (0 : ℝ)..r, kap ρ * J (fv ε v) ρ := by unfold G; ring
  rw [e]
  have key := int_pow_bound (continuous_kapJ (ε := ε) hv) (c := 12 * B) 0 r (fun ρ hρ => by
    have hρ' := mem_Icc_of_uIcc hA hB' hr hρ
    rw [abs_mul, abs_of_nonneg (kap_nonneg ρ), pow_zero, mul_one]
    have hJ : |J (fv ε v) ρ| ≤ 3 * B := by
      apply J_bound (continuous_fv hv) (by linarith [hρ'.1]) (by linarith [hρ'.2])
      intro τ hτ
      have hσ := mem_Icc_mul hA hB' hρ' hτ
      have hvσ : |v (ρ * τ)| ≤ 6 := by
        have := hva _ hσ
        rw [abs_le] at this ⊢; constructor <;> linarith [ha.1, ha.2, this.1, this.2]
      unfold fv
      rw [Nt_eq_of_abs_le hvσ, abs_mul, abs_of_nonneg (eta_nonneg _ _)]
      have := hB (ρ * τ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ (v (ρ * τ))
        (abs_le.1 hvσ)
      calc eta ε (ρ * τ) * |N (ρ * τ) (v (ρ * τ))| ≤ 1 * B :=
            mul_le_mul (eta_le_one _ _) this (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    calc kap ρ * |J (fv ε v) ρ| ≤ 4 * (3 * B) :=
          mul_le_mul (kap_le (by linarith [hρ'.2])) hJ (abs_nonneg _) (by norm_num)
      _ = 12 * B := by ring)
  have : |r| ≤ 2 * ε := abs_le.2 ⟨by linarith [hr.1], hr.2⟩
  refine key.trans ?_
  simp only [zero_add, pow_one, Nat.cast_zero, div_one]
  nlinarith

end P241S

end Estimates

section Fixed

/-!
# The fixed point of the Volterra operator (an iterate is a contraction)

Main output `master`: there is `ε > 0` and, for each slope `a ∈ [3,5]`, a continuous global
solution `V_a = G ε a V_a` with `|V_a - a| ≤ 1` on `[-2ε, 2ε]`, and `a ↦ V_a(1)` is Lipschitz.
-/

open Real Set MeasureTheory Filter Topology
open scoped ContDiff Nat NNReal

namespace P241S

section
variable {ε : ℝ} (hI : -2 * ε ≤ 1 + ε)

/-- extension of a function on the working interval to `ℝ` -/
noncomputable def ext (V : C(Icc (-2 * ε) (1 + ε), ℝ)) : ℝ → ℝ :=
  fun x => V (projIcc _ _ hI x)

lemma continuous_ext (V : C(Icc (-2 * ε) (1 + ε), ℝ)) : Continuous (ext hI V) :=
  V.continuous.comp continuous_projIcc

lemma ext_of_mem (V : C(Icc (-2 * ε) (1 + ε), ℝ)) {x : ℝ} (hx : x ∈ Icc (-2 * ε) (1 + ε)) :
    ext hI V x = V ⟨x, hx⟩ := by
  unfold ext; rw [projIcc_of_mem _ hx]

/-- the operator on the Banach space `C([-2ε, 1+ε])` -/
noncomputable def Phi (a : ℝ) (V : C(Icc (-2 * ε) (1 + ε), ℝ)) : C(Icc (-2 * ε) (1 + ε), ℝ) :=
  ⟨fun x => G ε a (ext hI V) x.1, (continuous_G (continuous_ext hI V)).comp continuous_subtype_val⟩

lemma Phi_apply (a : ℝ) (V : C(Icc (-2 * ε) (1 + ε), ℝ)) (x : Icc (-2 * ε) (1 + ε)) :
    Phi hI a V x = G ε a (ext hI V) x.1 := rfl

end

lemma abs_le_of_mem_I {ε x : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4) (hx : x ∈ Icc (-2 * ε) (1 + ε)) :
    |x| ≤ 1 + ε := abs_le.2 ⟨by linarith [hx.1], hx.2⟩

theorem master : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ Vf : ℝ → ℝ → ℝ,
    (∀ a ∈ Icc (3 : ℝ) 5, Continuous (Vf a) ∧ (∀ r, Vf a r = G ε a (Vf a) r) ∧
      (∀ σ ∈ Icc (-2 * ε) (2 * ε), |Vf a σ - a| ≤ 1)) ∧
    (∃ Cst : ℝ, ∀ a ∈ Icc (3 : ℝ) 5, ∀ b ∈ Icc (3 : ℝ) 5, |Vf a 1 - Vf b 1| ≤ Cst * |a - b|) := by
  obtain ⟨B, hB0, hB⟩ := N_bound
  set ε : ℝ := min (1 / 4) (1 / (24 * (B + 1))) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε' : ε ≤ 1 / 4 := min_le_left _ _
  have hεB : 24 * ε * B ≤ 1 := by
    have h1 : ε ≤ 1 / (24 * (B + 1)) := min_le_right _ _
    have h2 : 24 * ε * (B + 1) ≤ 1 := by
      calc 24 * ε * (B + 1) ≤ 24 * (1 / (24 * (B + 1))) * (B + 1) := by gcongr
        _ = 1 := by field_simp
    nlinarith
  obtain ⟨L, hL0, hLip⟩ := Nt_lip hε hε'
  have hI : -2 * ε ≤ 1 + ε := by linarith
  -- the iterate estimate
  set Q : ℝ := 12 * L * (1 + ε) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have iter : ∀ a : ℝ, ∀ k : ℕ, ∀ V1 V2 : C(Icc (-2 * ε) (1 + ε), ℝ), ∀ x : Icc (-2 * ε) (1 + ε),
      |(Phi hI a)^[k] V1 x - (Phi hI a)^[k] V2 x| ≤ dist V1 V2 * (12 * L * |x.1|) ^ k / k ! := by
    intro a k
    induction k with
    | zero =>
      intro V1 V2 x
      simpa [← Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := V1) (g := V2) x
    | succ k ih =>
      intro V1 V2 x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Phi_apply, Phi_apply]
      have := G_step hε hε' hL0 hLip (continuous_ext hI ((Phi hI a)^[k] V1))
        (continuous_ext hI ((Phi hI a)^[k] V2)) dist_nonneg k
        (fun σ hσ => by rw [ext_of_mem hI _ hσ, ext_of_mem hI _ hσ]; exact ih V1 V2 ⟨σ, hσ⟩) a a
        x.1 x.2
      simpa using this
  -- choose the iterate
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Q ^ k / k ! < 1 / 2 :=
    ((FloorSemiring.tendsto_pow_div_factorial_atTop Q).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  have hcontr : ∀ a : ℝ, ContractingWith (1 / 2 : ℝ≥0) ((Phi hI a)^[k]) := by
    intro a
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun V1 V2 => ?_
    rw [ContinuousMap.dist_le (by positivity)]
    intro x
    rw [Real.dist_eq]
    refine (iter a k V1 V2 x).trans ?_
    have hx := abs_le_of_mem_I hε hε' x.2
    have hxQ : 12 * L * |x.1| ≤ Q := by rw [hQ]; gcongr
    calc dist V1 V2 * (12 * L * |x.1|) ^ k / k ! ≤ dist V1 V2 * Q ^ k / k ! := by
          gcongr
      _ = dist V1 V2 * (Q ^ k / k !) := by ring
      _ ≤ dist V1 V2 * (1 / 2) := by gcongr
      _ = ((1 / 2 : ℝ≥0) : ℝ) * dist V1 V2 := by push_cast; ring
  set W : ℝ → C(Icc (-2 * ε) (1 + ε), ℝ) := fun a => ContractingWith.fixedPoint _ (hcontr a)
  have hWfix : ∀ a, Phi hI a (W a) = W a := fun a =>
    ContractingWith.isFixedPt_fixedPoint_iterate (hcontr a)
  -- the invariant set
  have hWB : ∀ a ∈ Icc (3 : ℝ) 5, ∀ x : Icc (-2 * ε) (1 + ε), x.1 ∈ Icc (-2 * ε) (2 * ε) →
      |W a x - a| ≤ 1 := by
    intro a ha
    set S : Set C(Icc (-2 * ε) (1 + ε), ℝ) :=
      {V | ∀ x : Icc (-2 * ε) (1 + ε), x.1 ∈ Icc (-2 * ε) (2 * ε) → |V x - a| ≤ 1} with hS
    have hSc : IsClosed S := by
      simp only [hS, Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_le (by fun_prop) continuous_const
    have hmap : MapsTo (Phi hI a) S S := by
      intro V hV x hx
      rw [Phi_apply]
      refine G_apriori hε hε' hB0 hB hεB ha (continuous_ext hI V) (fun σ hσ => ?_) x.1 hx
      have hσI : σ ∈ Icc (-2 * ε) (1 + ε) := ⟨hσ.1, by linarith [hσ.2]⟩
      rw [ext_of_mem hI V hσI]
      exact hV ⟨σ, hσI⟩ hσ
    have h0 : (ContinuousMap.const _ a : C(Icc (-2 * ε) (1 + ε), ℝ)) ∈ S := by
      intro x _; simp
    have hmapk : MapsTo ((Phi hI a)^[k]) S S := hmap.iterate k
    have hlim := (hcontr a).tendsto_iterate_fixedPoint (ContinuousMap.const _ a)
    exact hSc.mem_of_tendsto hlim (Eventually.of_forall fun n => hmapk.iterate n h0)
  -- parameter dependence of the iterates
  have hpar : ∀ a b : ℝ, ∀ j : ℕ, ∀ Z : C(Icc (-2 * ε) (1 + ε), ℝ),
      dist ((Phi hI a)^[j] Z) ((Phi hI b)^[j] Z) ≤ (1 + Q) ^ j * |a - b| := by
    intro a b j
    induction j with
    | zero => intro Z; simp
    | succ j ih =>
      intro Z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [ContinuousMap.dist_le (by positivity)]
      intro x
      rw [Real.dist_eq, Phi_apply, Phi_apply]
      set D := dist ((Phi hI a)^[j] Z) ((Phi hI b)^[j] Z)
      have := G_step hε hε' hL0 hLip (continuous_ext hI ((Phi hI a)^[j] Z))
        (continuous_ext hI ((Phi hI b)^[j] Z)) dist_nonneg 0
        (fun σ hσ => by
          rw [ext_of_mem hI _ hσ, ext_of_mem hI _ hσ]
          simpa [← Real.dist_eq] using ContinuousMap.dist_apply_le_dist (x := ⟨σ, hσ⟩)
            (f := (Phi hI a)^[j] Z) (g := (Phi hI b)^[j] Z)) a b x.1 x.2
      have hx := abs_le_of_mem_I hε hε' x.2
      refine this.trans ?_
      have hD := ih Z
      have h1 : D * (12 * L * |x.1|) ^ (0 + 1) / (0 + 1)! ≤ D * Q := by
        simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
        have hxQ : 12 * L * |x.1| ≤ Q := by rw [hQ]; gcongr
        gcongr
      have h2 : (1 : ℝ) ≤ (1 + Q) ^ j := one_le_pow₀ (by linarith)
      have h3 := abs_nonneg (a - b)
      calc |a - b| + D * (12 * L * |x.1|) ^ (0 + 1) / (0 + 1)! ≤ |a - b| + D * Q := by linarith
        _ ≤ (1 + Q) ^ j * |a - b| + (1 + Q) ^ j * |a - b| * Q := by
          gcongr
          · nlinarith
        _ = (1 + Q) ^ (j + 1) * |a - b| := by ring
  -- the global solutions
  refine ⟨ε, hε, hε', fun a => G ε a (ext hI (W a)), ?_, ?_⟩
  · intro a ha
    have hcont : Continuous (G ε a (ext hI (W a))) := continuous_G (continuous_ext hI (W a))
    have hagree : ∀ σ ∈ Icc (-2 * ε) (1 + ε), G ε a (ext hI (W a)) σ = ext hI (W a) σ := by
      intro σ hσ
      rw [ext_of_mem hI _ hσ]
      conv_rhs => rw [← hWfix a]
      rfl
    have hfv : fv ε (G ε a (ext hI (W a))) = fv ε (ext hI (W a)) := by
      funext σ
      unfold fv
      by_cases hσ : σ ∈ Icc (-2 * ε) (1 + ε)
      · rw [hagree σ hσ]
      · rcases not_and_or.1 hσ with h | h
        · rw [eta_eq_zero_of_le hε (by linarith [not_le.1 h])]; ring
        · rw [eta_eq_zero_of_ge hε (by linarith [not_le.1 h])]; ring
    refine ⟨hcont, fun r => ?_, fun σ hσ => ?_⟩
    · show G ε a (ext hI (W a)) r = G ε a (G ε a (ext hI (W a))) r
      simp only [G, hfv]
    · have hσI : σ ∈ Icc (-2 * ε) (1 + ε) := ⟨hσ.1, by linarith [hσ.2]⟩
      beta_reduce
      rw [hagree σ hσI, ext_of_mem hI _ hσI]
      exact hWB a ha ⟨σ, hσI⟩ hσ
  · refine ⟨(1 + Q) ^ k / (1 - ((1 / 2 : ℝ≥0) : ℝ)), fun a _ b _ => ?_⟩
    have h1I : (1 : ℝ) ∈ Icc (-2 * ε) (1 + ε) := ⟨by linarith, by linarith⟩
    have hval : ∀ c, G ε c (ext hI (W c)) 1 = W c ⟨1, h1I⟩ := by
      intro c
      conv_rhs => rw [← hWfix c]
      rfl
    beta_reduce
    rw [hval, hval, ← Real.dist_eq]
    refine (ContinuousMap.dist_apply_le_dist _).trans ?_
    have := (hcontr a).dist_fixedPoint_fixedPoint_of_dist_le' ((Phi hI b)^[k])
      (ContractingWith.fixedPoint_isFixedPt (hcontr a))
      (ContractingWith.fixedPoint_isFixedPt (hcontr b))
      (C := (1 + Q) ^ k * |a - b|) (fun Z => hpar a b k Z)
    calc dist (W a) (W b) ≤ _ := this
      _ = (1 + Q) ^ k / (1 - ((1 / 2 : ℝ≥0) : ℝ)) * |a - b| := by ring

end P241S

end Fixed

section Smooth

/-!
# Smoothness bootstrap for solutions of `v = G ε a v`, and the ODE in `r`
-/

open Real Set MeasureTheory Filter Topology
open scoped ContDiff Nat

namespace P241S

variable {ε a : ℝ} {v : ℝ → ℝ}

/-- Along a solution, the clamp is inactive. -/
lemma fv_eq (hε : 0 < ε) (ha : a ∈ Icc (3 : ℝ) 5)
    (hva : ∀ σ ∈ Icc (-2 * ε) (2 * ε), |v σ - a| ≤ 1) :
    fv ε v = fun σ => eta ε σ * N σ (v σ) := by
  funext σ
  unfold fv
  rcases le_or_gt (2 * ε) σ with h | h
  · rw [Nt_eq_of_ge hε h]
  rcases le_or_gt σ (-2 * ε) with h' | h'
  · rw [eta_eq_zero_of_le hε h', zero_mul, zero_mul]
  · have := hva σ ⟨h'.le, h.le⟩
    have h6 : |v σ| ≤ 6 := by
      rw [abs_le] at this ⊢; constructor <;> linarith [ha.1, ha.2, this.1, this.2]
    rw [Nt_eq_of_abs_le h6]

lemma hasDerivAt_sol (hv : Continuous v) (hfix : ∀ r, v r = G ε a v r) (r : ℝ) :
    HasDerivAt v (kap r * J (fv ε v) r) r := by
  have e : G ε a v = v := funext fun r => (hfix r).symm
  have := hasDerivAt_G (ε := ε) (a := a) hv r
  rwa [e] at this

lemma contDiff_sol (hε : 0 < ε) (ha : a ∈ Icc (3 : ℝ) 5) (hv : Continuous v)
    (hfix : ∀ r, v r = G ε a v r) (hva : ∀ σ ∈ Icc (-2 * ε) (2 * ε), |v σ - a| ≤ 1) :
    ContDiff ℝ ∞ v := by
  rw [contDiff_infty]
  intro n
  have hd : deriv v = fun r => kap r * J (fv ε v) r :=
    funext fun r => (hasDerivAt_sol hv hfix r).deriv
  induction n with
  | zero => rw [Nat.cast_zero, contDiff_zero]; exact hv
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun r => (hasDerivAt_sol hv hfix r).differentiableAt, by simp, ?_⟩
    rw [hd, fv_eq hε ha hva]
    have h1 : ContDiff ℝ n (fun σ => eta ε σ * N σ (v σ)) :=
      ((contDiff_infty.1 (contDiff_eta ε)) n).mul (contDiff_N_comp contDiff_id ih)
    exact ((contDiff_infty.1 contDiff_kap) n).mul (contDiff_J h1)

/-- The first integral: `q(r)² v'(r) = ∫₀ʳ q N(·, v)` on `(0, 1]`. -/
lemma first_integral (hε : 0 < ε) (ha : a ∈ Icc (3 : ℝ) 5) (hv : Continuous v)
    (hfix : ∀ r, v r = G ε a v r) (hva : ∀ σ ∈ Icc (-2 * ε) (2 * ε), |v σ - a| ≤ 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    qq r ^ 2 * deriv v r = ∫ σ in (0 : ℝ)..r, qq σ * N σ (v σ) := by
  rw [(hasDerivAt_sol hv hfix r).deriv, fv_eq hε ha hva, kap_eq (by linarith)]
  unfold J
  have hcomp := intervalIntegral.integral_comp_mul_left
    (a := 0) (b := 1) (fun σ => qq σ * (eta ε σ * N σ (v σ))) hr0.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at hcomp
  have e1 : (∫ τ in (0 : ℝ)..1, τ * (2 - r * τ) * (eta ε (r * τ) * N (r * τ) (v (r * τ))))
      = r⁻¹ * ∫ τ in (0 : ℝ)..1, qq (r * τ) * (eta ε (r * τ) * N (r * τ) (v (r * τ))) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext τ; unfold qq; field_simp
  have e2 : (∫ σ in (0 : ℝ)..r, qq σ * (eta ε σ * N σ (v σ)))
      = ∫ σ in (0 : ℝ)..r, qq σ * N σ (v σ) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [uIcc_of_le hr0.le] at hσ
    simp only
    rw [eta_eq_one hε (by linarith [hσ.1]) (by linarith [hσ.2]), one_mul]
  rw [e1, hcomp, e2]
  have h2r : (2 - r) ≠ 0 := by linarith
  unfold qq
  field_simp

/-- The second-order equation in `r`: `2 q' v' + q v'' = N(r, v)` on `(0, 1)`. -/
lemma ode_r (hε : 0 < ε) (ha : a ∈ Icc (3 : ℝ) 5) (hv : Continuous v)
    (hfix : ∀ r, v r = G ε a v r) (hva : ∀ σ ∈ Icc (-2 * ε) (2 * ε), |v σ - a| ≤ 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    2 * (2 - 2 * r) * deriv v r + qq r * deriv (deriv v) r = N r (v r) := by
  have hsm := contDiff_sol hε ha hv hfix hva
  have hd1 : Differentiable ℝ (deriv v) := by
    have h2 := contDiff_infty.1 hsm 2
    rw [show ((2:ℕ) : WithTop ℕ∞) = ((1:ℕ) : WithTop ℕ∞) + 1 by norm_num,
      contDiff_succ_iff_deriv] at h2
    exact h2.2.2.differentiable (by norm_num)
  -- derivative of q² v'
  have hP : HasDerivAt (fun r => qq r ^ 2 * deriv v r)
      (2 * qq r * (2 - 2 * r) * deriv v r + qq r ^ 2 * deriv (deriv v) r) r := by
    have hq : HasDerivAt qq (2 - 2 * r) r := by
      have := ((hasDerivAt_id' r).fun_mul ((hasDerivAt_id' r).const_sub 2))
      exact this.congr_deriv (by ring)
    have := (hq.fun_pow 2).fun_mul (hd1 r).hasDerivAt
    exact this.congr_deriv (by norm_num)
  have hcI : Continuous (fun σ => qq σ * N σ (v σ)) := by
    unfold qq; exact Continuous.mul (by fun_prop) (continuous_N.comp (continuous_id.prodMk hv))
  have hI : HasDerivAt (fun r => ∫ σ in (0 : ℝ)..r, qq σ * N σ (v σ)) (qq r * N r (v r)) r :=
    (hcI.integral_hasStrictDerivAt 0 r).hasDerivAt
  have heq : (fun r => qq r ^ 2 * deriv v r) =ᶠ[𝓝 r]
      (fun r => ∫ σ in (0 : ℝ)..r, qq σ * N σ (v σ)) := by
    filter_upwards [Ioo_mem_nhds hr0 hr1] with x hx
    exact first_integral hε ha hv hfix hva hx.1 hx.2.le
  have := hP.unique (hI.congr_of_eventuallyEq heq)
  have hq0 : 0 < qq r := by unfold qq; nlinarith
  have : qq r * (2 * (2 - 2 * r) * deriv v r + qq r * deriv (deriv v) r) = qq r * N r (v r) := by
    rw [← this]; ring
  exact mul_left_cancel₀ hq0.ne' this

end P241S

end Smooth

section Shoot

/-!
# From the `r`-solution to a shot `h(θ) = sin θ · V(1 - cos θ)`
-/

open Real Set Filter Topology
open scoped ContDiff

namespace P241S

variable {ε a : ℝ} {v : ℝ → ℝ}

lemma hasDerivAt_h {v : ℝ → ℝ} (hd : Differentiable ℝ v) (θ : ℝ) :
    HasDerivAt (fun θ => Real.sin θ * v (1 - Real.cos θ))
      (Real.cos θ * v (1 - Real.cos θ) + Real.sin θ * (deriv v (1 - Real.cos θ) * Real.sin θ)) θ := by
  have h1 : HasDerivAt (fun θ => 1 - Real.cos θ) (Real.sin θ) θ :=
    ((Real.hasDerivAt_cos θ).const_sub 1).congr_deriv (by ring)
  have h2 := (hd (1 - Real.cos θ)).hasDerivAt.comp θ h1
  exact (Real.hasDerivAt_sin θ).fun_mul h2

theorem shoot_of_sol (hε : 0 < ε) (ha : a ∈ Icc (3 : ℝ) 5) (hv : Continuous v)
    (hfix : ∀ r, v r = G ε a v r) (hva : ∀ σ ∈ Icc (-2 * ε) (2 * ε), |v σ - a| ≤ 1) :
    SphericalFerromagnet.ShootSol a (fun θ => Real.sin θ * v (1 - Real.cos θ)) ∧
      SphericalFerromagnet.PoleRep (fun θ => Real.sin θ * v (1 - Real.cos θ)) := by
  have hsm := contDiff_sol hε ha hv hfix hva
  have hd : Differentiable ℝ v := hsm.differentiable (by simp)
  have hd1 : Differentiable ℝ (deriv v) := by
    have h2 := contDiff_infty.1 hsm 2
    rw [show ((2:ℕ) : WithTop ℕ∞) = ((1:ℕ) : WithTop ℕ∞) + 1 by norm_num,
      contDiff_succ_iff_deriv] at h2
    exact h2.2.2.differentiable (by norm_num)
  have hv0 : v 0 = a := by rw [hfix 0]; simp [G]
  set h : ℝ → ℝ := fun θ => Real.sin θ * v (1 - Real.cos θ) with hh
  have hderiv : deriv h = fun θ => Real.cos θ * v (1 - Real.cos θ)
      + Real.sin θ * (deriv v (1 - Real.cos θ) * Real.sin θ) :=
    funext fun θ => (hasDerivAt_h hd θ).deriv
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- smoothness
    apply ContDiff.contDiffOn
    exact Real.contDiff_sin.mul (hsm.comp (contDiff_const.sub Real.contDiff_cos))
  · simp [hh]
  · have hpi : (0 : ℝ) < π / 2 := by positivity
    rw [(hasDerivAt_h hd 0).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hpi 0 ⟨le_rfl, hpi.le⟩)]
    simp [hv0]
  · intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hc1 : Real.cos θ < 1 := by
      have := Real.sin_sq_add_cos_sq θ; nlinarith
    -- second derivative
    have h1 : HasDerivAt (fun θ => 1 - Real.cos θ) (Real.sin θ) θ :=
      ((Real.hasDerivAt_cos θ).const_sub 1).congr_deriv (by ring)
    have hA := (hd (1 - Real.cos θ)).hasDerivAt.comp θ h1
    have hB := (hd1 (1 - Real.cos θ)).hasDerivAt.comp θ h1
    have h2 : HasDerivAt (deriv h)
        (-Real.sin θ * v (1 - Real.cos θ) + Real.cos θ * (deriv v (1 - Real.cos θ) * Real.sin θ)
          + (Real.cos θ * (deriv v (1 - Real.cos θ) * Real.sin θ) + Real.sin θ *
            ((deriv (deriv v) (1 - Real.cos θ) * Real.sin θ) * Real.sin θ
              + deriv v (1 - Real.cos θ) * Real.cos θ))) θ := by
      rw [hderiv]
      exact ((Real.hasDerivAt_cos θ).fun_mul hA).add
        ((Real.hasDerivAt_sin θ).fun_mul (hB.fun_mul (Real.hasDerivAt_sin θ)))
    have hrel := ode_r hε ha hv hfix hva (r := 1 - Real.cos θ) (by linarith) (by linarith)
    have hq : qq (1 - Real.cos θ) = Real.sin θ ^ 2 := by
      unfold qq; nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hq] at hrel
    have hN := N_theta (θ := θ) (g := v (1 - Real.cos θ)) hs.ne'
    unfold SphericalFerromagnet.profileOperator
    rw [h2.deriv, hderiv]
    simp only [hh]
    have hsc := Real.sin_sq_add_cos_sq θ
    generalize v (1 - Real.cos θ) = g at *
    generalize deriv v (1 - Real.cos θ) = V1 at *
    generalize deriv (deriv v) (1 - Real.cos θ) = V2 at *
    generalize N (1 - Real.cos θ) g = NN at *
    generalize Real.sin (2 * (Real.sin θ * g) - 2 * θ) = U at *
    generalize Real.sin (2 * (Real.sin θ * g)) = T at *
    field_simp
    field_simp at hN
    linear_combination 2 * Real.sin θ ^ 3 * hrel + hN + 2 * Real.sin θ * g * hsc
  · -- pole representation
    refine ⟨π / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩,
      fun x => C ((1 - x ^ 2) * v (1 - x) ^ 2),
      fun x => v (1 - x) * S ((1 - x ^ 2) * v (1 - x) ^ 2), ?_, ?_, ?_⟩
    · apply ContDiff.contDiffOn
      have hv' : ContDiff ℝ ∞ (fun x => v (1 - x)) := hsm.comp (by fun_prop)
      have : ContDiff ℝ ∞ (fun x : ℝ => (1 - x ^ 2) * v (1 - x) ^ 2) := by fun_prop
      exact contDiff_C.comp this
    · apply ContDiff.contDiffOn
      have hv' : ContDiff ℝ ∞ (fun x => v (1 - x)) := hsm.comp (by fun_prop)
      have : ContDiff ℝ ∞ (fun x : ℝ => (1 - x ^ 2) * v (1 - x) ^ 2) := by fun_prop
      exact hv'.mul (contDiff_S.comp this)
    · intro θ _
      have e : (1 - Real.cos θ ^ 2) * v (1 - Real.cos θ) ^ 2
          = (Real.sin θ * v (1 - Real.cos θ)) ^ 2 := by
        rw [mul_pow, Real.sin_sq]
      simp only [hh, e]
      refine ⟨(C_sq _).symm, ?_⟩
      rw [← S_sq]; ring

end P241S

end Shoot

section UniqueFacts

/-!
# Basic facts about an arbitrary shot (for uniqueness)
-/

open Real Set Filter Topology
open scoped ContDiff

namespace P241S

/-- the right-hand side of `h'' = F(θ, h, h')` -/
noncomputable def rhs (t x p : ℝ) : ℝ :=
  -(Real.cos t / Real.sin t) * p + Real.sin (2 * x) / (2 * Real.sin t ^ 2)
    + 2 * Real.sin (2 * x - 2 * t)

lemma pi2_pos : (0 : ℝ) < π / 2 := by positivity

structure ShotFacts (a : ℝ) (h : ℝ → ℝ) : Prop where
  cont : ContinuousOn h (Icc 0 (π / 2))
  contd : ContinuousOn (derivWithin h (Icc 0 (π / 2))) (Icc 0 (π / 2))
  diffOn : DifferentiableOn ℝ h (Icc 0 (π / 2))
  zero : h 0 = 0
  slope : derivWithin h (Icc 0 (π / 2)) 0 = a
  hd : ∀ t ∈ Ioo (0 : ℝ) (π / 2), HasDerivAt h (derivWithin h (Icc 0 (π / 2)) t) t
  hdd : ∀ t ∈ Ioo (0 : ℝ) (π / 2), HasDerivAt (derivWithin h (Icc 0 (π / 2)))
    (rhs t (h t) (derivWithin h (Icc 0 (π / 2)) t)) t

theorem shotFacts {a : ℝ} {h : ℝ → ℝ} (hs : SphericalFerromagnet.ShootSol a h) : ShotFacts a h := by
  obtain ⟨hcd, h0, hslope, hode⟩ := hs
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc pi2_pos
  have hdw : ∀ t ∈ Ioo (0 : ℝ) (π / 2), derivWithin h (Icc 0 (π / 2)) t = deriv h t :=
    fun t ht => derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hoo : ContDiffOn ℝ ∞ h (Ioo 0 (π / 2)) := hcd.mono Ioo_subset_Icc_self
  have hd1 : ContDiffOn ℝ ∞ (deriv h) (Ioo 0 (π / 2)) :=
    hoo.deriv_of_isOpen isOpen_Ioo (by simp)
  refine ⟨hcd.continuousOn, hcd.continuousOn_derivWithin hU (by simp),
    hcd.differentiableOn (by simp), h0, hslope, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hdw t ht]
    exact ((hcd.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)).hasDerivAt
  · have heq : derivWithin h (Icc 0 (π / 2)) =ᶠ[𝓝 t] deriv h := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx using hdw x hx
    have hda : HasDerivAt (deriv h) (deriv (deriv h) t) t :=
      ((hd1.contDiffAt (Ioo_mem_nhds ht.1 ht.2)).differentiableAt (by simp)).hasDerivAt
    refine (hda.congr_of_eventuallyEq heq).congr_deriv ?_
    have := hode t ht
    unfold SphericalFerromagnet.profileOperator at this
    unfold rhs
    rw [hdw t ht]
    linarith

/-- `|(sin x - x) - (sin y - y)| ≤ |x - y| · max(x², y²) / 2`. -/
lemma sin_sub_id_lip (x y : ℝ) :
    |(Real.sin x - x) - (Real.sin y - y)| ≤ |x - y| * (max (x ^ 2) (y ^ 2) / 2) := by
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun t => Real.sin t - t) (f' := fun t => Real.cos t - 1) (s := uIcc y x)
    (C := max (x ^ 2) (y ^ 2) / 2)
    (fun t _ => ((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [Real.cos_le_one t])]
      have h1 := Real.one_sub_sq_div_two_le_cos (x := t)
      have h2 : t ^ 2 ≤ max (x ^ 2) (y ^ 2) := by
        have : |t| ≤ max |x| |y| := by
          rcases le_total y x with h | h
          · rw [uIcc_of_le h] at ht
            rw [abs_le]; constructor
            · have := neg_abs_le y; have := le_max_right |x| |y|; linarith [ht.1]
            · have := le_abs_self x; have := le_max_left |x| |y|; linarith [ht.2]
          · rw [uIcc_of_ge h] at ht
            rw [abs_le]; constructor
            · have := neg_abs_le x; have := le_max_left |x| |y|; linarith [ht.1]
            · have := le_abs_self y; have := le_max_right |x| |y|; linarith [ht.2]
        rcases le_total |x| |y| with h | h
        · rw [max_eq_right h] at this
          have := sq_le_sq' (by linarith [abs_nonneg t, neg_abs_le t, le_abs_self t] :
            -|y| ≤ t) (by linarith [le_abs_self t] : t ≤ |y|)
          rw [sq_abs] at this
          exact this.trans (le_max_right _ _)
        · rw [max_eq_left h] at this
          have := sq_le_sq' (by linarith [abs_nonneg t, neg_abs_le t, le_abs_self t] :
            -|x| ≤ t) (by linarith [le_abs_self t] : t ≤ |x|)
          rw [sq_abs] at this
          exact this.trans (le_max_left _ _)
      linarith)
    (convex_uIcc y x) left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  linarith [hmv]

end P241S

end UniqueFacts

section UniqueSing

/-!
# Uniqueness of shots near the singular point `θ = 0`

For two shots `h₁, h₂` with the same slope, `w = h₁ - h₂` satisfies, with
`P = sin² θ · w' - sin θ cos θ · w`, `|P'| ≤ K sin² θ |w|` and `(w / sin θ)' = P / sin³ θ`.
An iteration gives `|w| ≤ D 2⁻ⁿ sin θ` on `(0, θ₀]` for every `n`.
-/

open Real Set Filter Topology Asymptotics
open scoped ContDiff

namespace P241S

lemma le_pi_div_two_mul_sin {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) : t ≤ π / 2 * Real.sin t := by
  have := Real.mul_le_sin h0 h1
  have hpi := Real.pi_pos
  calc t = π / 2 * (2 / π * t) := by field_simp
    _ ≤ π / 2 * Real.sin t := by gcongr

lemma sin_le_sin_of_le' {x y : ℝ} (h0 : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 2) :
    Real.sin x ≤ Real.sin y :=
  Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hy hxy

/-- linear bound `|h t| ≤ C t` for a shot. -/
lemma shot_linear_bound {a : ℝ} {h : ℝ → ℝ} (F : ShotFacts a h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) (π / 2), |h t| ≤ C * t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn F.contd
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_derivWithin_le F.diffOn
    (fun x hx => (hC x hx).trans (le_max_left C 0)) (convex_Icc 0 (π / 2))
    (left_mem_Icc.2 pi2_pos.le) ht
  rw [F.zero, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
  exact this

theorem unique_near_zero {a : ℝ} {h₁ h₂ : ℝ → ℝ} (F₁ : ShotFacts a h₁) (F₂ : ShotFacts a h₂) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ θ₀ ≤ 1 ∧ ∀ t ∈ Icc 0 θ₀, h₁ t = h₂ t := by
  set I := Icc (0 : ℝ) (π / 2) with hI
  have hpi := Real.pi_pos
  have hpi2 : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC₁0, hC₁⟩ := shot_linear_bound F₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := shot_linear_bound F₂
  set C := max C₁ C₂
  have hC0 : 0 ≤ C := le_max_of_le_left hC₁0
  have hb₁ : ∀ t ∈ I, |h₁ t| ≤ C * t := fun t ht =>
    (hC₁ t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.1)
  have hb₂ : ∀ t ∈ I, |h₂ t| ≤ C * t := fun t ht =>
    (hC₂ t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ht.1)
  set w : ℝ → ℝ := fun t => h₁ t - h₂ t with hw
  set d₁ := derivWithin h₁ I
  set d₂ := derivWithin h₂ I
  set dw : ℝ → ℝ := fun t => d₁ t - d₂ t with hdw
  set D : ℝ := π * C
  have hD0 : 0 ≤ D := by positivity
  have hwD : ∀ t ∈ I, |w t| ≤ D * Real.sin t := by
    intro t ht
    have := le_pi_div_two_mul_sin ht.1 ht.2
    calc |w t| ≤ |h₁ t| + |h₂ t| := abs_sub _ _
      _ ≤ C * t + C * t := add_le_add (hb₁ t ht) (hb₂ t ht)
      _ ≤ 2 * C * (π / 2 * Real.sin t) := by nlinarith
      _ = D * Real.sin t := by ring
  set K : ℝ := 2 * C ^ 2 * (π / 2) ^ 2 + 6
  have hK0 : 0 ≤ K := by positivity
  -- the auxiliary function P and its derivative
  set P : ℝ → ℝ := fun t => Real.sin t ^ 2 * dw t - Real.sin t * Real.cos t * w t with hP
  set Q : ℝ → ℝ := fun t => ((Real.sin (2 * h₁ t) - 2 * h₁ t) - (Real.sin (2 * h₂ t) - 2 * h₂ t)) / 2
    + 2 * Real.sin t ^ 2 * w t
    + 2 * Real.sin t ^ 2 * (Real.sin (2 * h₁ t - 2 * t) - Real.sin (2 * h₂ t - 2 * t)) with hQ
  have hPd : ∀ t ∈ Ioo (0 : ℝ) (π / 2), HasDerivAt P (Q t) t := by
    intro t ht
    have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2])).ne'
    have e1 := ((Real.hasDerivAt_sin t).fun_pow 2).fun_mul ((F₁.hdd t ht).sub (F₂.hdd t ht))
    have e2 := ((Real.hasDerivAt_sin t).fun_mul (Real.hasDerivAt_cos t)).fun_mul
      ((F₁.hd t ht).sub (F₂.hd t ht))
    refine (e1.sub e2).congr_deriv ?_
    simp only [hQ, rhs, hw, Pi.sub_apply]
    have hsc := Real.sin_sq_add_cos_sq t
    field_simp
    linear_combination (-2 * (h₁ t - h₂ t)) * hsc
  have hQb : ∀ t ∈ Ioo (0 : ℝ) (π / 2), |Q t| ≤ K * Real.sin t ^ 2 * |w t| := by
    intro t ht
    have htI : t ∈ I := Ioo_subset_Icc_self ht
    have hs0 : 0 ≤ Real.sin t ^ 2 := sq_nonneg _
    have hst := le_pi_div_two_mul_sin htI.1 htI.2
    have t1 : |((Real.sin (2 * h₁ t) - 2 * h₁ t) - (Real.sin (2 * h₂ t) - 2 * h₂ t)) / 2|
        ≤ 2 * C ^ 2 * (π / 2) ^ 2 * Real.sin t ^ 2 * |w t| := by
      have := sin_sub_id_lip (2 * h₁ t) (2 * h₂ t)
      have hm : max ((2 * h₁ t) ^ 2) ((2 * h₂ t) ^ 2) ≤ 4 * (C * t) ^ 2 := by
        apply max_le
        · have := hb₁ t htI; rw [mul_pow, ← sq_abs (h₁ t)]
          have : |h₁ t| ^ 2 ≤ (C * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          linarith
        · have := hb₂ t htI; rw [mul_pow, ← sq_abs (h₂ t)]
          have : |h₂ t| ^ 2 ≤ (C * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          linarith
      have hCt : (C * t) ^ 2 ≤ C ^ 2 * (π / 2) ^ 2 * Real.sin t ^ 2 := by
        rw [mul_pow, mul_assoc]
        gcongr
        rw [← mul_pow]
        exact pow_le_pow_left₀ htI.1 hst 2
      have e : 2 * h₁ t - 2 * h₂ t = 2 * w t := by simp [hw]; ring
      rw [abs_div, abs_two]
      rw [e, abs_mul, abs_two] at this
      calc _ ≤ 2 * |w t| * (max ((2 * h₁ t) ^ 2) ((2 * h₂ t) ^ 2) / 2) / 2 := by gcongr
        _ ≤ 2 * |w t| * (4 * (C * t) ^ 2 / 2) / 2 := by gcongr
        _ ≤ 2 * |w t| * (4 * (C ^ 2 * (π / 2) ^ 2 * Real.sin t ^ 2) / 2) / 2 := by gcongr
        _ = _ := by ring
    have t3 : |2 * Real.sin t ^ 2 * (Real.sin (2 * h₁ t - 2 * t) - Real.sin (2 * h₂ t - 2 * t))|
        ≤ 4 * Real.sin t ^ 2 * |w t| := by
      have := Real.abs_sin_sub_sin_le (2 * h₁ t - 2 * t) (2 * h₂ t - 2 * t)
      have e : 2 * h₁ t - 2 * t - (2 * h₂ t - 2 * t) = 2 * w t := by simp [hw]; ring
      rw [e, abs_mul, abs_two] at this
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hs0]
      nlinarith
    have t2 : |2 * Real.sin t ^ 2 * w t| = 2 * Real.sin t ^ 2 * |w t| := by
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hs0]
    calc |Q t| ≤ |((Real.sin (2 * h₁ t) - 2 * h₁ t) - (Real.sin (2 * h₂ t) - 2 * h₂ t)) / 2|
          + |2 * Real.sin t ^ 2 * w t|
          + |2 * Real.sin t ^ 2 * (Real.sin (2 * h₁ t - 2 * t) - Real.sin (2 * h₂ t - 2 * t))| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ 2 * C ^ 2 * (π / 2) ^ 2 * Real.sin t ^ 2 * |w t| + 2 * Real.sin t ^ 2 * |w t|
          + 4 * Real.sin t ^ 2 * |w t| := by rw [t2]; gcongr
      _ = K * Real.sin t ^ 2 * |w t| := by ring
  -- choice of θ₀
  set θ₀ : ℝ := min 1 (1 / (2 * K + 2)) with hθdef
  have hθ0 : 0 < θ₀ := lt_min one_pos (by positivity)
  have hθ1 : θ₀ ≤ 1 := min_le_left _ _
  have hθpi : θ₀ < π / 2 := lt_of_le_of_lt hθ1 hpi2
  have hKθ : K * θ₀ ^ 2 ≤ 1 / 2 := by
    have h1 : θ₀ ≤ 1 / (2 * K + 2) := min_le_right _ _
    have h2 : θ₀ ^ 2 ≤ θ₀ := by nlinarith
    have h3 : K * θ₀ ≤ 1 / 2 := by
      calc K * θ₀ ≤ K * (1 / (2 * K + 2)) := by gcongr
        _ ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    nlinarith
  -- continuity of `P`
  have hPc : ContinuousOn P I := by
    have hwc : ContinuousOn w I := F₁.cont.sub F₂.cont
    have hdwc : ContinuousOn dw I := F₁.contd.sub F₂.contd
    exact ((Real.continuous_sin.pow 2).continuousOn.mul hdwc).sub
      ((Real.continuous_sin.mul Real.continuous_cos).continuousOn.mul hwc)
  have hP0 : P 0 = 0 := by simp [hP]
  -- `w = o(θ)` at `0`
  have hw0 : HasDerivWithinAt w 0 I 0 := by
    have e1 := (F₁.diffOn 0 (left_mem_Icc.2 pi2_pos.le)).hasDerivWithinAt
    have e2 := (F₂.diffOn 0 (left_mem_Icc.2 pi2_pos.le)).hasDerivWithinAt
    have := e1.sub e2
    rw [F₁.slope, F₂.slope, sub_self] at this
    exact this
  have hsmall : ∀ η > 0, ∀ t > 0, ∃ x ∈ Ioo 0 t, |w x| ≤ η * x := by
    intro η hη t ht
    have hlo := hw0.isLittleO
    have hw00 : w 0 = 0 := by simp [hw, F₁.zero, F₂.zero]
    simp only [hw00, sub_zero, smul_zero] at hlo
    have hev := hlo.def hη
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[I] 0 := by
      apply nhdsWithin_le_of_mem
      exact mem_of_superset (Ioo_mem_nhdsGT pi2_pos) Ioo_subset_Icc_self
    obtain ⟨x, hx1, hx2⟩ := ((hev.filter_mono hle).and (Ioo_mem_nhdsGT ht)).exists
    refine ⟨x, hx2, ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx2.1] at hx1
    exact hx1
  -- derivative of `w / sin`
  have hu : ∀ x ∈ Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun y => w y / Real.sin y) (P x / Real.sin x ^ 3) x := by
    intro x hx
    have hs : Real.sin x ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])).ne'
    refine (((F₁.hd x hx).sub (F₂.hd x hx)).div (Real.hasDerivAt_sin x) hs).congr_deriv ?_
    simp only [hP, hdw, hw, Pi.sub_apply, d₁, d₂, hI]
    generalize derivWithin h₁ (Icc 0 (π / 2)) x = A
    generalize derivWithin h₂ (Icc 0 (π / 2)) x = B
    field_simp
  -- the iteration
  have iter : ∀ n : ℕ, ∀ t ∈ Ioc 0 θ₀, |w t| ≤ D * (1 / 2) ^ n * Real.sin t := by
    intro n
    induction n with
    | zero => intro t ht; simpa using hwD t ⟨ht.1.le, by linarith [ht.2]⟩
    | succ n ih =>
      intro t ht
      set Dn := D * (1 / 2) ^ n with hDn
      have hDn0 : 0 ≤ Dn := by positivity
      have hPb : ∀ x ∈ Ioc 0 θ₀, |P x| ≤ K * Dn * Real.sin x ^ 3 * x := by
        intro x hx
        obtain ⟨c, hc, hcq⟩ := exists_hasDerivAt_eq_slope P Q hx.1
          (hPc.mono (Icc_subset_Icc le_rfl (by linarith [hx.2])))
          (fun y hy => hPd y ⟨hy.1, by linarith [hy.2, hx.2]⟩)
        rw [hP0, sub_zero, sub_zero] at hcq
        have hPx : P x = Q c * x := by rw [hcq, div_mul_cancel₀ _ hx.1.ne']
        have hcI : c ∈ Ioo (0 : ℝ) (π / 2) := ⟨hc.1, by linarith [hc.2, hx.2]⟩
        have hsc0 : 0 ≤ Real.sin c := (Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hcI.2])).le
        have hscx : Real.sin c ≤ Real.sin x := sin_le_sin_of_le' hc.1.le hc.2.le (by linarith [hx.2])
        have hwc := ih c ⟨hc.1, by linarith [hc.2, hx.2]⟩
        rw [hPx, abs_mul, abs_of_pos hx.1]
        apply mul_le_mul_of_nonneg_right _ hx.1.le
        calc |Q c| ≤ K * Real.sin c ^ 2 * |w c| := hQb c hcI
          _ ≤ K * Real.sin c ^ 2 * (Dn * Real.sin c) := by gcongr
          _ = K * Dn * Real.sin c ^ 3 := by ring
          _ ≤ K * Dn * Real.sin x ^ 3 := by gcongr
      have htI : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨ht.1, by linarith [ht.2]⟩
      have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [htI.2])
      -- bound on `w t / sin t`
      have hut : |w t / Real.sin t| ≤ K * Dn * t ^ 2 := by
        apply le_of_forall_pos_le_add
        intro η hη
        obtain ⟨x, hx, hwx⟩ := hsmall (η / 2) (by positivity) t ht.1
        have hxI : x ∈ Ioo (0 : ℝ) (π / 2) := ⟨hx.1, by linarith [hx.2, htI.2]⟩
        have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hxI.2])
        obtain ⟨c, hc, hcq⟩ := exists_hasDerivAt_eq_slope (fun y => w y / Real.sin y)
          (fun y => P y / Real.sin y ^ 3) hx.2
          (fun y hy => (hu y ⟨by linarith [hy.1, hx.1], by linarith [hy.2, htI.2]⟩).continuousAt.continuousWithinAt)
          (fun y hy => hu y ⟨by linarith [hy.1, hx.1], by linarith [hy.2, htI.2]⟩)
        have hc0 : 0 < c := by linarith [hc.1, hx.1]
        have hsc : 0 < Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc0 (by linarith [hc.2, htI.2])
        have hPc' := hPb c ⟨hc0, by linarith [hc.2, ht.2]⟩
        have hbc : |P c / Real.sin c ^ 3| ≤ K * Dn * t := by
          rw [abs_div, abs_of_pos (by positivity : 0 < Real.sin c ^ 3), div_le_iff₀ (by positivity)]
          calc |P c| ≤ K * Dn * Real.sin c ^ 3 * c := hPc'
            _ ≤ K * Dn * Real.sin c ^ 3 * t := by gcongr; linarith [hc.2]
            _ = K * Dn * t * Real.sin c ^ 3 := by ring
        have hdiff : |w t / Real.sin t - w x / Real.sin x| ≤ K * Dn * t ^ 2 := by
          have e : w t / Real.sin t - w x / Real.sin x = P c / Real.sin c ^ 3 * (t - x) := by
            rw [hcq]; field_simp [(sub_pos.2 hx.2).ne']
          rw [e, abs_mul, abs_of_pos (sub_pos.2 hx.2)]
          have hKt : 0 ≤ K * Dn * t := mul_nonneg (mul_nonneg hK0 hDn0) ht.1.le
          calc |P c / Real.sin c ^ 3| * (t - x) ≤ K * Dn * t * (t - x) :=
                mul_le_mul_of_nonneg_right hbc (sub_pos.2 hx.2).le
            _ ≤ K * Dn * t * t := mul_le_mul_of_nonneg_left (by linarith [hx.1]) hKt
            _ = K * Dn * t ^ 2 := by ring
        have hux : |w x / Real.sin x| ≤ η := by
          rw [abs_div, abs_of_pos hsx, div_le_iff₀ hsx]
          have := le_pi_div_two_mul_sin hx.1.le hxI.2.le
          calc |w x| ≤ η / 2 * x := hwx
            _ ≤ η / 2 * (π / 2 * Real.sin x) := by gcongr
            _ ≤ η / 2 * (2 * Real.sin x) := by gcongr; linarith [Real.pi_lt_four]
            _ = η * Real.sin x := by ring
        calc |w t / Real.sin t| ≤ |w t / Real.sin t - w x / Real.sin x| + |w x / Real.sin x| := by
              have := abs_sub_abs_le_abs_sub (w t / Real.sin t) (w x / Real.sin x)
              linarith
          _ ≤ K * Dn * t ^ 2 + η := add_le_add hdiff hux
      rw [abs_div, abs_of_pos hst, div_le_iff₀ hst] at hut
      have ht2 : t ^ 2 ≤ θ₀ ^ 2 := pow_le_pow_left₀ ht.1.le ht.2 2
      calc |w t| ≤ K * Dn * t ^ 2 * Real.sin t := hut
        _ ≤ K * Dn * θ₀ ^ 2 * Real.sin t := by gcongr
        _ = (K * θ₀ ^ 2) * Dn * Real.sin t := by ring
        _ ≤ (1 / 2) * Dn * Real.sin t := by gcongr
        _ = D * (1 / 2) ^ (n + 1) * Real.sin t := by rw [hDn, pow_succ]; ring
  refine ⟨θ₀, hθ0, hθ1, fun t ht => ?_⟩
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0, F₁.zero, F₂.zero]
  · have hlim : Tendsto (fun n : ℕ => D * (1 / 2) ^ n * Real.sin t) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul D
      simpa using this.mul_const (Real.sin t)
    have : |w t| ≤ 0 := ge_of_tendsto' hlim (fun n => iter n t ⟨h0, ht.2⟩)
    have := abs_nonpos_iff.1 this
    simp only [hw] at this
    linarith

end P241S

end UniqueSing

section UniqueReg

/-!
# Uniqueness of shots away from the pole (Grönwall via Mathlib's `ODE_solution_unique`)
-/

open Real Set Filter Topology
open scoped ContDiff NNReal

namespace P241S

theorem unique_regular {a : ℝ} {h₁ h₂ : ℝ → ℝ} (F₁ : ShotFacts a h₁) (F₂ : ShotFacts a h₂)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀' : t₀ < π / 2) (he : h₁ t₀ = h₂ t₀)
    (hed : derivWithin h₁ (Icc 0 (π / 2)) t₀ = derivWithin h₂ (Icc 0 (π / 2)) t₀) :
    ∀ t ∈ Icc t₀ (π / 2), h₁ t = h₂ t := by
  set I := Icc (0 : ℝ) (π / 2)
  have hs0 : 0 < Real.sin t₀ := Real.sin_pos_of_pos_of_lt_pi ht₀ (by linarith [Real.pi_pos])
  set s₀ := Real.sin t₀
  set Kr : ℝ := 1 / s₀ + 1 / s₀ ^ 2 + 4 + 1
  set vf : ℝ → ℝ × ℝ → ℝ × ℝ := fun t y => (y.2, rhs t y.1 y.2)
  have hLip : ∀ t ∈ Ico t₀ (π / 2), LipschitzOnWith (Real.toNNReal Kr) (vf t) univ := by
    intro t ht
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hst : s₀ ≤ Real.sin t := sin_le_sin_of_le' ht₀.le ht.1 ht.2.le
    have hs : 0 < Real.sin t := lt_of_lt_of_le hs0 hst
    have hc0 : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht₀, ht.1], ht.2.le⟩
    have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
    have hKr : (0 : ℝ) ≤ Kr := by positivity
    rw [Real.coe_toNNReal _ hKr, Prod.dist_eq, Prod.dist_eq]
    simp only [vf, Real.dist_eq]
    set m := max |y.1 - z.1| |y.2 - z.2|
    have hm1 : |y.1 - z.1| ≤ m := le_max_left _ _
    have hm2 : |y.2 - z.2| ≤ m := le_max_right _ _
    have hm0 : 0 ≤ m := (abs_nonneg _).trans hm1
    have hK1 : 1 ≤ Kr := by
      have := one_div_pos.2 hs0; have := one_div_pos.2 (pow_pos hs0 2)
      simp only [Kr]; linarith
    apply max_le
    · calc |y.2 - z.2| ≤ 1 * m := by linarith
        _ ≤ Kr * m := by gcongr
    · have e : rhs t y.1 y.2 - rhs t z.1 z.2 = -(Real.cos t / Real.sin t) * (y.2 - z.2)
          + (Real.sin (2 * y.1) - Real.sin (2 * z.1)) / (2 * Real.sin t ^ 2)
          + 2 * (Real.sin (2 * y.1 - 2 * t) - Real.sin (2 * z.1 - 2 * t)) := by
        unfold rhs; ring
      rw [e]
      have b1 : |-(Real.cos t / Real.sin t) * (y.2 - z.2)| ≤ 1 / s₀ * m := by
        rw [abs_mul, abs_neg, abs_div, abs_of_nonneg hc0, abs_of_pos hs]
        have : Real.cos t / Real.sin t ≤ 1 / s₀ :=
          div_le_div₀ zero_le_one hc1 hs0 hst
        exact mul_le_mul this hm2 (abs_nonneg _) (by positivity)
      have b2 : |(Real.sin (2 * y.1) - Real.sin (2 * z.1)) / (2 * Real.sin t ^ 2)| ≤ 1 / s₀ ^ 2 * m := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sin t ^ 2)]
        have h1 := Real.abs_sin_sub_sin_le (2 * y.1) (2 * z.1)
        rw [show 2 * y.1 - 2 * z.1 = 2 * (y.1 - z.1) by ring, abs_mul, abs_two] at h1
        rw [div_le_iff₀ (by positivity)]
        have hs2 : s₀ ^ 2 ≤ Real.sin t ^ 2 := pow_le_pow_left₀ hs0.le hst 2
        have : 1 / s₀ ^ 2 * m * (2 * s₀ ^ 2) = 2 * m := by field_simp
        calc |Real.sin (2 * y.1) - Real.sin (2 * z.1)| ≤ 2 * m := by linarith
          _ = 1 / s₀ ^ 2 * m * (2 * s₀ ^ 2) := this.symm
          _ ≤ 1 / s₀ ^ 2 * m * (2 * Real.sin t ^ 2) := by gcongr
      have b3 : |2 * (Real.sin (2 * y.1 - 2 * t) - Real.sin (2 * z.1 - 2 * t))| ≤ 4 * m := by
        have h1 := Real.abs_sin_sub_sin_le (2 * y.1 - 2 * t) (2 * z.1 - 2 * t)
        rw [show 2 * y.1 - 2 * t - (2 * z.1 - 2 * t) = 2 * (y.1 - z.1) by ring, abs_mul,
          abs_two] at h1
        rw [abs_mul, abs_two]; linarith
      calc _ ≤ |-(Real.cos t / Real.sin t) * (y.2 - z.2)|
            + |(Real.sin (2 * y.1) - Real.sin (2 * z.1)) / (2 * Real.sin t ^ 2)|
            + |2 * (Real.sin (2 * y.1 - 2 * t) - Real.sin (2 * z.1 - 2 * t))| :=
            (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
        _ ≤ 1 / s₀ * m + 1 / s₀ ^ 2 * m + 4 * m := add_le_add (add_le_add b1 b2) b3
        _ ≤ Kr * m := by simp only [Kr]; nlinarith
  set f₁ : ℝ → ℝ × ℝ := fun t => (h₁ t, derivWithin h₁ I t)
  set f₂ : ℝ → ℝ × ℝ := fun t => (h₂ t, derivWithin h₂ I t)
  have hsub : Icc t₀ (π / 2) ⊆ I := Icc_subset_Icc ht₀.le le_rfl
  have hder : ∀ {h : ℝ → ℝ}, ShotFacts a h → ∀ t ∈ Ico t₀ (π / 2),
      HasDerivWithinAt (fun t => (h t, derivWithin h I t))
        (vf t (h t, derivWithin h I t)) (Ici t) t := by
    intro h F t ht
    have htI : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨by linarith [ht.1], ht.2⟩
    exact ((F.hd t htI).prodMk (F.hdd t htI)).hasDerivWithinAt
  have hEq := ODE_solution_unique_of_mem_Icc_right (v := vf) (s := fun _ => univ) hLip
    ((F₁.cont.mono hsub).prodMk (F₁.contd.mono hsub)) (hder F₁) (fun _ _ => mem_univ _)
    ((F₂.cont.mono hsub).prodMk (F₂.contd.mono hsub)) (hder F₂) (fun _ _ => mem_univ _)
    (Prod.ext he hed)
  intro t ht
  exact congrArg Prod.fst (hEq ht)

end P241S

end UniqueReg

section Main

/-!
# (S1) and (S2): existence, uniqueness and continuous dependence of the shots

The statements below are verbatim those of
`Theorems/Thm_SphericalFerromagnet_shoot_exists.lean` and
`Theorems/Thm_SphericalFerromagnet_shoot_endpoint_continuous.lean`.
-/

open scoped ContDiff
open Real Set Filter Topology

namespace P241S

/-- Uniqueness of shots on `[0, π/2]`. -/
theorem shoot_unique {a : ℝ} {h₁ h₂ : ℝ → ℝ} (hs₁ : SphericalFerromagnet.ShootSol a h₁)
    (hs₂ : SphericalFerromagnet.ShootSol a h₂) : ∀ t ∈ Icc 0 (π / 2), h₁ t = h₂ t := by
  have F₁ := shotFacts hs₁
  have F₂ := shotFacts hs₂
  obtain ⟨θ₀, hθ0, hθ1, hnear⟩ := unique_near_zero F₁ F₂
  have hpi2 : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  set t₀ := θ₀ / 2 with ht₀def
  have ht0 : 0 < t₀ := by positivity
  have ht0' : t₀ < π / 2 := by linarith
  have hloc : h₁ =ᶠ[𝓝 t₀] h₂ := by
    filter_upwards [Ioo_mem_nhds ht0 (by linarith [ht₀def] : t₀ < θ₀)] with x hx
    exact hnear x ⟨hx.1.le, hx.2.le⟩
  have hd : derivWithin h₁ (Icc 0 (π / 2)) t₀ = derivWithin h₂ (Icc 0 (π / 2)) t₀ := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht0 ht0'),
      derivWithin_of_mem_nhds (Icc_mem_nhds ht0 ht0'), hloc.deriv_eq]
  have hreg := unique_regular F₁ F₂ ht0 ht0' (hloc.eq_of_nhds) hd
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hnear t ⟨ht.1, by linarith [ht₀def]⟩
  · exact hreg t ⟨h, ht.2⟩

/-- Existence with the explicit Lipschitz dependence of the endpoint. -/
theorem shoot_family : ∃ H : ℝ → ℝ → ℝ,
    (∀ a ∈ Icc (3 : ℝ) 5, SphericalFerromagnet.ShootSol a (H a) ∧
      SphericalFerromagnet.PoleRep (H a)) ∧
    ∃ Cst : ℝ, ∀ a ∈ Icc (3 : ℝ) 5, ∀ b ∈ Icc (3 : ℝ) 5,
      |H a (π / 2) - H b (π / 2)| ≤ Cst * |a - b| := by
  obtain ⟨ε, hε, -, Vf, hV, Cst, hC⟩ := master
  refine ⟨fun a θ => Real.sin θ * Vf a (1 - Real.cos θ), fun a ha => ?_, Cst, fun a ha b hb => ?_⟩
  · obtain ⟨hc, hfix, hva⟩ := hV a ha
    exact shoot_of_sol hε ha hc hfix hva
  · simpa [Real.sin_pi_div_two, Real.cos_pi_div_two] using hC a ha b hb

end P241S


end Main

open Real Set
open scoped ContDiff

theorem solution :
    ∃ Φ : ℝ → ℝ, ContinuousOn Φ (Icc 3 5) ∧
      ∀ a ∈ Icc (3 : ℝ) 5, ∀ h, SphericalFerromagnet.ShootSol a h → h (π / 2) = Φ a := by
  obtain ⟨H, hH, Cst, hC⟩ := P241S.shoot_family
  refine ⟨fun a => H a (π / 2), ?_, fun a ha h hs => ?_⟩
  · intro a ha
    rw [Metric.continuousWithinAt_iff]
    intro η hη
    refine ⟨η / (|Cst| + 1), by positivity, fun {b} hb hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    calc |H b (π / 2) - H a (π / 2)| ≤ Cst * |b - a| := hC b hb a ha
      _ ≤ |Cst| * |b - a| := by gcongr; exact le_abs_self _
      _ ≤ (|Cst| + 1) * |b - a| := by gcongr; linarith
      _ < (|Cst| + 1) * (η / (|Cst| + 1)) := by gcongr
      _ = η := by field_simp
  · exact P241S.shoot_unique hs (hH a ha).1 (π / 2) ⟨by positivity, le_rfl⟩

