-- Prove2me | solution 1 for PhiSobBayes.theorem_3_1_forward_lc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:41:14.600892+00:00
-- url     : https://prove2.me/submissions/5b817cbb-e8f9-4d7b-8a76-804fc343b182

import Mathlib
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_AdmissiblePhi
import Definitions.Def_PhiSobBayes_testClass
import Definitions.Def_PhiSobBayes_phiEnt
import Definitions.Def_PhiSobBayes_PhiSobolev
import Theorems.Thm_PhiSobBayes_lemma_A_19
import Definitions.Def_PhiSobBayes_posterior
import Definitions.Def_PhiSobBayes_gamObs
import Definitions.Def_PhiSobBayes_IsStronglyLogConcave
import Definitions.Def_LogConcaveOn
import Theorems.Thm_ConvexOptimization_prekopa_marginal_log_concave
import Theorems.Thm_PhiSobBayes_lemma_6_2
import Theorems.Thm_PhiSobBayes_fact_A_22
import Theorems.Thm_PhiSobBayes_lemma_6_1
import Definitions.Def_PhiSobBayes_IsLogConcave

-- ===== Defs.lean =====
section

/-!
# Gaussian-channel ("stochastic localization") objects in the natural parametrization

For a prior `π` on `E = ℝⁿ`, SNR `t ≥ 0` and natural parameter `θ ∈ E`:
* `wt t θ x = exp(⟪θ, x⟫ - t ‖x‖² / 2)` (likelihood in natural parameters),
* `Zt π t θ = ∫ wt t θ x dπ(x)` (normaliser),
* `post π t θ = π.withDensity (wt t θ · / Zt π t θ)` (posterior),
* `pmean π t θ g = ∫ g d(post π t θ)` (posterior mean of `g`),
* `pcov π t θ g = ∫ (g x - pmean π t θ g) • x d(post π t θ)` (covariance of `g` with `X`, a vector),
* `Qt π t` = law of `tX + √t G` with `X ∼ π`, `G ∼ N(0, I)` independent (the law of the
  natural observation `θ = √t Y_t`).
The paper's posterior is `PhiSobBayes.posterior μ t y = post μ t (√t • y)`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace PSBSL

variable {n : ℕ}

/-- likelihood in natural parameters -/
def wt (t : ℝ) (θ x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (⟪θ, x⟫ - t * ‖x‖ ^ 2 / 2)

/-- normaliser -/
def Zt (π : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x, wt t θ x ∂π

/-- posterior -/
def post (π : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  π.withDensity (fun x => ENNReal.ofReal (wt t θ x / Zt π t θ))

/-- posterior mean of `g` -/
def pmean (π : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, g x ∂(post π t θ)

/-- posterior covariance of `g` with the identity `X` (a vector) -/
def pcov (π : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) :=
  ∫ x, (g x - pmean π t θ g) • x ∂(post π t θ)

/-- law of the natural observation `t X + √t G` -/
def Qt (π : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (π.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => t • p.1 + Real.sqrt t • p.2)

end PSBSL

end
end

-- ===== Basic.lean =====
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace PSBSL

variable {n : ℕ}

/-! ### 1. Elementary properties of `wt` -/

theorem wt_pos (t : ℝ) (θ x : EuclideanSpace ℝ (Fin n)) : 0 < wt t θ x := Real.exp_pos _

theorem wt_nonneg (t : ℝ) (θ x : EuclideanSpace ℝ (Fin n)) : 0 ≤ wt t θ x := (wt_pos t θ x).le

theorem inner_le_quad {s : ℝ} (hs : 0 < s) (θ x : EuclideanSpace ℝ (Fin n)) :
    ⟪θ, x⟫ ≤ ‖θ‖ ^ 2 / (2 * s) + s * ‖x‖ ^ 2 / 2 := by
  have h1 := real_inner_le_norm θ x
  have h3 : ‖θ‖ ^ 2 / (2 * s) + s * ‖x‖ ^ 2 / 2 - ‖θ‖ * ‖x‖ = (‖θ‖ - s * ‖x‖) ^ 2 / (2 * s) := by
    field_simp; ring
  have h4 : 0 ≤ (‖θ‖ - s * ‖x‖) ^ 2 / (2 * s) := by positivity
  linarith

theorem wt_le {t : ℝ} (ht : 0 < t) (θ x : EuclideanSpace ℝ (Fin n)) :
    wt t θ x ≤ Real.exp (‖θ‖ ^ 2 / (2 * t)) := by
  unfold wt
  apply Real.exp_le_exp.2
  have := inner_le_quad ht θ x
  linarith

theorem pow_mul_exp_neg_le {t : ℝ} (ht : 0 < t) (k : ℕ) (r : ℝ) :
    r ^ k * Real.exp (-(t * r ^ 2 / 4)) ≤ 1 + (Nat.factorial k) * (4 / t) ^ k := by
  set a := t * r ^ 2 / 4 with ha_def
  have ha : 0 ≤ a := by positivity
  have hfac := Real.pow_div_factorial_le_exp a ha k
  have hfpos : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
  have h1 : a ^ k ≤ Nat.factorial k * Real.exp a := by
    rw [div_le_iff₀ hfpos] at hfac; linarith
  have hr2 : (r ^ 2) ^ k = (4 / t) ^ k * a ^ k := by
    rw [← mul_pow]; congr 1; rw [ha_def]; field_simp
  have hrk : r ^ k ≤ 1 + (r ^ 2) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    nlinarith [sq_nonneg (r ^ k - 1)]
  have he : 0 < Real.exp (-a) := Real.exp_pos _
  have he1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : a ^ k * Real.exp (-a) ≤ Nat.factorial k := by
    have : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
    calc a ^ k * Real.exp (-a) ≤ (Nat.factorial k * Real.exp a) * Real.exp (-a) :=
          mul_le_mul_of_nonneg_right h1 he.le
      _ = Nat.factorial k := by rw [mul_assoc, this, mul_one]
  have h4t : 0 ≤ (4 / t) ^ k := by positivity
  calc r ^ k * Real.exp (-a) ≤ (1 + (r ^ 2) ^ k) * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right hrk he.le
    _ = Real.exp (-a) + (4 / t) ^ k * (a ^ k * Real.exp (-a)) := by rw [hr2]; ring
    _ ≤ 1 + (4 / t) ^ k * Nat.factorial k := by gcongr
    _ = _ := by ring

theorem norm_pow_mul_wt_le {t : ℝ} (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ∃ C, ∀ x, ‖x‖ ^ k * wt t θ x ≤ C := by
  refine ⟨Real.exp (‖θ‖ ^ 2 / t) * (1 + (Nat.factorial k) * (4 / t) ^ k), fun x => ?_⟩
  have h2t : 0 < t / 2 := by positivity
  have hq := inner_le_quad h2t θ x
  have hw : wt t θ x ≤ Real.exp (‖θ‖ ^ 2 / t) * Real.exp (-(t * ‖x‖ ^ 2 / 4)) := by
    unfold wt
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : ‖θ‖ ^ 2 / (2 * (t / 2)) = ‖θ‖ ^ 2 / t := by congr 1; ring
    rw [this] at hq
    linarith
  have hb := pow_mul_exp_neg_le ht k ‖x‖
  calc ‖x‖ ^ k * wt t θ x ≤ ‖x‖ ^ k * (Real.exp (‖θ‖ ^ 2 / t) * Real.exp (-(t * ‖x‖ ^ 2 / 4))) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = Real.exp (‖θ‖ ^ 2 / t) * (‖x‖ ^ k * Real.exp (-(t * ‖x‖ ^ 2 / 4))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le

@[fun_prop]
theorem continuous_wt_comp {α : Type*} [TopologicalSpace α] {T : α → ℝ}
    {f g : α → EuclideanSpace ℝ (Fin n)} (hT : Continuous T) (hf : Continuous f)
    (hg : Continuous g) : Continuous (fun a => wt (T a) (f a) (g a)) := by
  unfold wt; fun_prop

@[fun_prop]
theorem measurable_wt_comp {α : Type*} [MeasurableSpace α] {T : α → ℝ}
    {f g : α → EuclideanSpace ℝ (Fin n)} (hT : Measurable T) (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun a => wt (T a) (f a) (g a)) := by
  unfold wt; fun_prop

theorem continuous_wt (t : ℝ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => wt t p.1 p.2) := by
  fun_prop

theorem continuous_wt_uncurry :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      wt p.1 p.2.1 p.2.2) := by
  fun_prop

theorem measurable_wt (t : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => wt t p.1 p.2) := by
  fun_prop

theorem measurable_wt_uncurry :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      wt p.1 p.2.1 p.2.2) := by
  fun_prop

theorem continuous_wt_right (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : Continuous (wt t θ) := by
  fun_prop

theorem measurable_wt_right (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : Measurable (wt t θ) := by
  fun_prop

theorem wt_add (t r : ℝ) (θ θ' x : EuclideanSpace ℝ (Fin n)) :
    wt t θ x * wt r θ' x = wt (t + r) (θ + θ') x := by
  unfold wt; rw [← Real.exp_add, inner_add_left]; ring_nf

/-! ### 2. Integrability -/

variable {π : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure π] {t : ℝ}

theorem integrable_wt (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n)) : Integrable (wt t θ) π := by
  refine Integrable.of_bound (continuous_wt_right t θ).aestronglyMeasurable
    (Real.exp (‖θ‖ ^ 2 / (2 * t))) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (wt_pos t θ x)]
  exact wt_le ht θ x

theorem integrable_mul_wt (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : AEStronglyMeasurable g π)
    (hgb : ∃ C k, ∀ x, |g x| ≤ C * (1 + ‖x‖ ^ k)) :
    Integrable (fun x => g x * wt t θ x) π := by
  obtain ⟨C, k, hC⟩ := hgb
  obtain ⟨D, hD⟩ := norm_pow_mul_wt_le ht θ k
  refine Integrable.of_bound (hg.mul (continuous_wt_right t θ).aestronglyMeasurable)
    (|C| * (Real.exp (‖θ‖ ^ 2 / (2 * t)) + D)) (Filter.Eventually.of_forall fun x => ?_)
  have hw := wt_pos t θ x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]
  have h1 : |g x| ≤ |C| * (1 + ‖x‖ ^ k) :=
    (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  calc |g x| * wt t θ x ≤ |C| * (1 + ‖x‖ ^ k) * wt t θ x := mul_le_mul_of_nonneg_right h1 hw.le
    _ = |C| * (wt t θ x + ‖x‖ ^ k * wt t θ x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (wt_le ht θ x) (hD x)) (abs_nonneg C)

/-! ### 3. The normaliser -/

theorem Zt_pos (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n)) : 0 < Zt π t θ :=
  integral_exp_pos (integrable_wt ht θ)

omit [IsProbabilityMeasure π] in
theorem Zt_nonneg (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : 0 ≤ Zt π t θ :=
  integral_nonneg fun x => wt_nonneg t θ x

theorem continuous_Zt (ht : 0 < t) : Continuous (Zt π t) := by
  rw [continuous_iff_continuousAt]
  intro θ₀
  refine continuousAt_of_dominated (bound := fun _ => Real.exp ((‖θ₀‖ + 1) ^ 2 / (2 * t)))
    (Filter.Eventually.of_forall fun θ => (continuous_wt_right t θ).aestronglyMeasurable) ?_
    (integrable_const _) (Filter.Eventually.of_forall fun x => ?_)
  · filter_upwards [Metric.ball_mem_nhds θ₀ one_pos] with θ hθ
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (wt_pos t θ x)]
    refine (wt_le ht θ x).trans (Real.exp_le_exp.2 ?_)
    have h1 : ‖θ‖ ≤ ‖θ₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' θ θ₀
      rw [Metric.mem_ball, dist_eq_norm] at hθ
      linarith
    gcongr
  · exact (show Continuous fun θ => wt t θ x by fun_prop).continuousAt

theorem measurable_Zt (ht : 0 < t) : Measurable (Zt π t) := (continuous_Zt ht).measurable

/-! ### 4. The posterior -/

omit [IsProbabilityMeasure π] in
theorem measurable_post_density (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun x => ENNReal.ofReal (wt t θ x / Zt π t θ)) := by
  fun_prop

theorem post_isProb (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n)) :
    IsProbabilityMeasure (post π t θ) := by
  constructor
  rw [post, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_wt ht θ).div_const _)
      (Filter.Eventually.of_forall fun x => div_nonneg (wt_nonneg t θ x) (Zt_nonneg t θ)),
    integral_div]
  change ENNReal.ofReal (Zt π t θ / Zt π t θ) = 1
  rw [div_self (Zt_pos ht θ).ne', ENNReal.ofReal_one]

omit [IsProbabilityMeasure π] in
/-- Integral against the posterior (no integrability needed). -/
theorem integral_post' (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, g x ∂(post π t θ) = (∫ x, g x * wt t θ x ∂π) / Zt π t θ := by
  rw [post, integral_withDensity_eq_integral_toReal_smul (measurable_post_density t θ)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (div_nonneg (wt_nonneg t θ x) (Zt_nonneg t θ)), smul_eq_mul]
  ring

set_option linter.unusedVariables false in
omit [IsProbabilityMeasure π] in
theorem integral_post (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hint : Integrable (fun x => g x * wt t θ x) π) :
    ∫ x, g x ∂(post π t θ) = (∫ x, g x * wt t θ x ∂π) / Zt π t θ :=
  integral_post' t θ g

omit [IsProbabilityMeasure π] in
theorem pmean_eq (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    pmean π t θ g = (∫ x, g x * wt t θ x ∂π) / Zt π t θ :=
  integral_post' t θ g

omit [IsProbabilityMeasure π] in
theorem integrable_post_iff (θ : EuclideanSpace ℝ (Fin n)) {g : EuclideanSpace ℝ (Fin n) → ℝ} :
    Integrable g (post π t θ) ↔ Integrable (fun x => g x * wt t θ x / Zt π t θ) π := by
  rw [post, integrable_withDensity_iff_integrable_smul' (measurable_post_density t θ)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (div_nonneg (wt_nonneg t θ x) (Zt_nonneg t θ)), smul_eq_mul]
  ring

theorem integrable_post (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : AEStronglyMeasurable g π)
    (hgb : ∃ C k, ∀ x, |g x| ≤ C * (1 + ‖x‖ ^ k)) : Integrable g (post π t θ) :=
  (integrable_post_iff θ).2 ((integrable_mul_wt ht θ hg hgb).div_const _)

omit [IsProbabilityMeasure π] in
theorem integrable_post_of_integrable (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Integrable g π) : Integrable g (post π t θ) := by
  rw [integrable_post_iff]
  have : Integrable (fun x => wt t θ x / Zt π t θ * g x) π :=
    hg.bdd_mul (c := Real.exp (‖θ‖ ^ 2 / (2 * t)) / Zt π t θ)
      ((show Continuous (fun x => wt t θ x / Zt π t θ) by fun_prop).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (wt_nonneg t θ x) (Zt_nonneg t θ))]
        exact div_le_div_of_nonneg_right (wt_le ht θ x) (Zt_nonneg t θ))
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only; ring

omit [IsProbabilityMeasure π] in
theorem post_absolutelyContinuous (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : post π t θ ≪ π :=
  withDensity_absolutelyContinuous _ _

/-! ### 5. The standard Gaussian density and the representation of `Qt` -/

omit [IsProbabilityMeasure π] in
theorem SL_lintegral_fin_prod {m : ℕ} (μ : Fin m → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin m → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction m with
  | zero => simp
  | succ m m_ih =>
      calc
        _ = ∫⁻ x : ℝ × (Fin m → ℝ), f 0 x.1 * ∏ i : Fin m, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, Fin.cons_zero]
          rfl
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin m, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← m_ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf _),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact Finset.aemeasurable_fun_prod _
            (fun (i : Fin m) _ => ((hf i.succ).comp (measurable_pi_apply i)).aemeasurable)
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

omit [IsProbabilityMeasure π] in
theorem SL_pi_gaussianReal (m : ℕ) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1) =
      volume.withDensity (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  refine Measure.pi_eq (μ := fun _ : Fin m => gaussianReal 0 1) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    SL_lintegral_fin_prod _ _ (fun _ => measurable_gaussianPDF 0 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ (hs i)]

omit [IsProbabilityMeasure π] in
theorem SL_prod_gaussianPDF (m : ℕ) (x : Fin m → ℝ) :
    ∏ i, gaussianPDF 0 1 (x i) = ENNReal.ofReal ((2 * Real.pi) ^ (-(m : ℝ) / 2) *
      Real.exp (-‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ ^ 2 / 2)) := by
  simp only [gaussianPDF, gaussianPDFReal]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, EuclideanSpace.norm_sq_eq]
  congr 1
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity),
      ← Real.rpow_mul_natCast (by positivity)]
    congr 1
    · simp
    · ring
  · congr 1
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs, neg_div]

/-- density of the standard Gaussian on `ℝⁿ` w.r.t. Lebesgue measure -/
def gaussDens (m : ℕ) (g : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(m : ℝ) / 2) * Real.exp (-‖g‖ ^ 2 / 2))

omit [IsProbabilityMeasure π] in
theorem measurable_gaussDens (m : ℕ) : Measurable (gaussDens m) := by
  unfold gaussDens; fun_prop

omit [IsProbabilityMeasure π] in
theorem stdGaussian_eq_withDensity (m : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) = volume.withDensity (gaussDens m) := by
  rw [← map_pi_eq_stdGaussian, SL_pi_gaussianReal]
  ext s hs
  rw [Measure.map_apply (WithLp.measurable_toLp 2 _) hs,
    withDensity_apply _ (hs.preimage (WithLp.measurable_toLp 2 _)), withDensity_apply _ hs,
    ← (PiLp.volume_preserving_toLp (Fin m)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding]
  congr 1
  funext x
  exact SL_prod_gaussianPDF m x

omit [IsProbabilityMeasure π] in
theorem gaussDens_sub (a u : EuclideanSpace ℝ (Fin n)) :
    gaussDens n (u - a) = gaussDens n u * ENNReal.ofReal (Real.exp (⟪a, u⟫ - ‖a‖ ^ 2 / 2)) := by
  unfold gaussDens
  rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add, norm_sub_sq_real,
    real_inner_comm]
  congr 3
  ring

omit [IsProbabilityMeasure π] in
/-- Cameron–Martin: shifting the standard Gaussian. -/
theorem lintegral_stdGaussian_add (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f)
    (a : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ g, f (a + g) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫⁻ u, f u * ENNReal.ofReal (Real.exp (⟪a, u⟫ - ‖a‖ ^ 2 / 2))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hφ := measurable_gaussDens n
  rw [stdGaussian_eq_withDensity, lintegral_withDensity_eq_lintegral_mul _ hφ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hφ (by fun_prop)]
  calc ∫⁻ g, (gaussDens n * fun g => f (a + g)) g
        = ∫⁻ g, (fun u => gaussDens n (u - a) * f u) (a + g) := by
          congr 1; funext g; simp
    _ = ∫⁻ u, gaussDens n (u - a) * f u :=
          lintegral_add_left_eq_self (fun u => gaussDens n (u - a) * f u) a
    _ = _ := by
          congr 1; funext u
          simp only [Pi.mul_apply, gaussDens_sub]
          ring

theorem isProb_Qt (t : ℝ) : IsProbabilityMeasure (Qt π t) := by
  unfold Qt
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem lintegral_Qt (ht : 0 < t) (h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ θ, h θ ∂(Qt π t) = ∫⁻ u, h (Real.sqrt t • u) * ENNReal.ofReal (Zt π t (Real.sqrt t • u))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [Qt, lintegral_map hh (by fun_prop), lintegral_prod _ (by fun_prop)]
  have inner : ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ g, h (t • x + Real.sqrt t • g) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫⁻ u, h (Real.sqrt t • u) * ENNReal.ofReal (wt t (Real.sqrt t • u) x)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    intro x
    have := lintegral_stdGaussian_add (fun u => h (Real.sqrt t • u)) (by fun_prop)
      (Real.sqrt t • x)
    simp only [smul_add, smul_smul, Real.mul_self_sqrt ht.le] at this
    rw [this]
    congr 1; funext u
    congr 2
    unfold wt
    rw [inner_smul_left, inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt ht.le, real_inner_comm]
  simp_rw [inner]
  rw [lintegral_lintegral_swap (by fun_prop)]
  congr 1; funext u
  rw [lintegral_const_mul _ (by fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_wt ht _)
      (Filter.Eventually.of_forall fun x => wt_nonneg t _ x)]
  rfl

theorem Qt_eq (ht : 0 < t) :
    Qt π t = ((stdGaussian (EuclideanSpace ℝ (Fin n))).withDensity
      (fun u => ENNReal.ofReal (Zt π t (Real.sqrt t • u)))).map (fun u => Real.sqrt t • u) := by
  have hZ := measurable_Zt (π := π) ht
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_Qt ht f hf, lintegral_map hf (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  congr 1; funext u
  simp only [Pi.mul_apply]
  ring

theorem integral_Qt (ht : 0 < t) (h : EuclideanSpace ℝ (Fin n) → ℝ) (hint : Integrable h (Qt π t)) :
    ∫ θ, h θ ∂(Qt π t) = ∫ u, h (Real.sqrt t • u) * Zt π t (Real.sqrt t • u)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hZ := measurable_Zt (π := π) ht
  have hm := hint.1
  rw [Qt_eq ht] at hm ⊢
  rw [integral_map (by fun_prop) hm, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1; funext u
  rw [ENNReal.toReal_ofReal (Zt_nonneg t _), smul_eq_mul, mul_comm]

/-! ### 6. Tower property (Nishimori identity) -/

omit [IsProbabilityMeasure π] in
theorem Zt_dirac (t : ℝ) (θ x : EuclideanSpace ℝ (Fin n)) :
    Zt (Measure.dirac x) t θ = wt t θ x := by
  unfold Zt; rw [integral_dirac]

omit [IsProbabilityMeasure π] in
/-- Gaussian moment generating function in the form needed for the tower property. -/
theorem lintegral_wt_stdGaussian (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ u, ENNReal.ofReal (wt t (Real.sqrt t • u) x) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 1 := by
  have h1 := lintegral_Qt (π := Measure.dirac x) ht (fun _ => 1) measurable_const
  have := isProb_Qt (π := Measure.dirac x) t
  simp only [lintegral_const, measure_univ, one_mul, Zt_dirac] at h1
  exact h1.symm

omit [IsProbabilityMeasure π] in
theorem integral_wt_stdGaussian (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ∫ u, wt t (Real.sqrt t • u) x ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => wt_nonneg t _ x)
    (by fun_prop), lintegral_wt_stdGaussian ht x, ENNReal.toReal_one]

omit [IsProbabilityMeasure π] in
theorem lintegral_post_eq (t : ℝ) (θ : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(post π t θ) = ∫⁻ x, ENNReal.ofReal (wt t θ x / Zt π t θ) * g x ∂π := by
  rw [post, lintegral_withDensity_eq_lintegral_mul _ (measurable_post_density t θ) hg]
  rfl

theorem measurable_lintegral_post (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hg : Measurable g) : Measurable (fun θ => ∫⁻ x, g x ∂(post π t θ)) := by
  have hZ := measurable_Zt (π := π) ht
  simp_rw [lintegral_post_eq t _ hg]
  exact Measurable.lintegral_prod_right' (f := fun p : EuclideanSpace ℝ (Fin n) ×
    EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (wt t p.1 p.2 / Zt π t p.1) * g p.2) (by fun_prop)

theorem lintegral_post_Qt (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ θ, ∫⁻ x, g x ∂(post π t θ) ∂(Qt π t) = ∫⁻ x, g x ∂π := by
  have hZ := measurable_Zt (π := π) ht
  rw [lintegral_Qt ht _ (measurable_lintegral_post ht hg)]
  have key : ∀ u : EuclideanSpace ℝ (Fin n),
      (∫⁻ x, g x ∂(post π t (Real.sqrt t • u))) * ENNReal.ofReal (Zt π t (Real.sqrt t • u)) =
      ∫⁻ x, g x * ENNReal.ofReal (wt t (Real.sqrt t • u) x) ∂π := by
    intro u
    rw [lintegral_post_eq t _ hg, ← lintegral_mul_const _ (by fun_prop)]
    congr 1; funext x
    rw [mul_comm _ (g x), mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (wt_nonneg _ _ _)
      (Zt_nonneg _ _)), div_mul_cancel₀ _ (Zt_pos ht _).ne']
  simp_rw [key]
  rw [lintegral_lintegral_swap (by fun_prop)]
  congr 1; funext x
  rw [lintegral_const_mul _ (by fun_prop), lintegral_wt_stdGaussian ht x, mul_one]

/-- Tower property for nonnegative integrable measurable `g`. -/
theorem integral_pmean_Qt_of_nonneg (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g π) :
    Integrable (fun θ => pmean π t θ g) (Qt π t) ∧
      ∫ θ, pmean π t θ g ∂(Qt π t) = ∫ x, g x ∂π := by
  have := isProb_Qt (π := π) t
  have hpm : ∀ θ, ENNReal.ofReal (pmean π t θ g) = ∫⁻ x, ENNReal.ofReal (g x) ∂(post π t θ) :=
    fun θ => ofReal_integral_eq_lintegral_ofReal (integrable_post_of_integrable ht θ hgi)
      (Filter.Eventually.of_forall hg0)
  have hpm0 : ∀ θ, 0 ≤ pmean π t θ g := fun θ => integral_nonneg hg0
  have hmeas : Measurable (fun θ => pmean π t θ g) := by
    have : (fun θ => pmean π t θ g) =
        fun θ => (∫⁻ x, ENNReal.ofReal (g x) ∂(post π t θ)).toReal := by
      funext θ; rw [← hpm, ENNReal.toReal_ofReal (hpm0 θ)]
    rw [this]
    exact (measurable_lintegral_post ht hgm.ennreal_ofReal).ennreal_toReal
  have hlin : ∫⁻ θ, ENNReal.ofReal (pmean π t θ g) ∂(Qt π t) = ∫⁻ x, ENNReal.ofReal (g x) ∂π := by
    simp_rw [hpm]
    exact lintegral_post_Qt ht hgm.ennreal_ofReal
  have hint : Integrable (fun θ => pmean π t θ g) (Qt π t) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpm0), hlin]
    exact hgi.lintegral_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpm0)
      hmeas.aestronglyMeasurable, hlin,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgi.1]

omit [IsProbabilityMeasure π] in
theorem pmean_congr_ae (t : ℝ) (θ : EuclideanSpace ℝ (Fin n)) {g g' : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : g =ᵐ[π] g') : pmean π t θ g = pmean π t θ g' :=
  integral_congr_ae ((post_absolutelyContinuous t θ).ae_le h)

omit [IsProbabilityMeasure π] in
theorem pmean_sub (ht : 0 < t) (θ : EuclideanSpace ℝ (Fin n)) {g g' : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Integrable g π) (hg' : Integrable g' π) :
    pmean π t θ (fun x => g x - g' x) = pmean π t θ g - pmean π t θ g' :=
  integral_sub (integrable_post_of_integrable ht θ hg) (integrable_post_of_integrable ht θ hg')

private theorem pmean_Qt_aux (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Integrable g π) :
    Integrable (fun θ => pmean π t θ g) (Qt π t) ∧
      ∫ θ, pmean π t θ g ∂(Qt π t) = ∫ x, g x ∂π := by
  set g' := hg.1.mk g with hg'_def
  have hg'm : Measurable g' := hg.1.stronglyMeasurable_mk.measurable
  have hae : g =ᵐ[π] g' := hg.1.ae_eq_mk
  have hg'i : Integrable g' π := hg.congr hae
  have e1 : (fun θ => pmean π t θ g) = fun θ => pmean π t θ g' :=
    funext fun θ => pmean_congr_ae t θ hae
  have hp := hg'i.pos_part
  have hn := hg'i.neg_part
  have e2 : (fun θ => pmean π t θ g') = fun θ =>
      pmean π t θ (fun x => max (g' x) 0) - pmean π t θ (fun x => max (-g' x) 0) := by
    funext θ
    rw [← pmean_sub ht θ hp hn]
    simp only [max_zero_sub_max_neg_zero_eq_self]
  obtain ⟨hi1, he1⟩ := integral_pmean_Qt_of_nonneg ht (g := fun x => max (g' x) 0)
    (by fun_prop) (fun x => le_max_right _ _) hp
  obtain ⟨hi2, he2⟩ := integral_pmean_Qt_of_nonneg ht (g := fun x => max (-g' x) 0)
    (by fun_prop) (fun x => le_max_right _ _) hn
  rw [e1, e2]
  refine ⟨hi1.sub hi2, ?_⟩
  rw [integral_sub hi1 hi2, he1, he2, ← integral_sub hp hn, integral_congr_ae hae]
  simp only [max_zero_sub_max_neg_zero_eq_self]

theorem integrable_pmean_Qt (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Integrable g π) : Integrable (fun θ => pmean π t θ g) (Qt π t) :=
  (pmean_Qt_aux ht hg).1

theorem integral_pmean_Qt (ht : 0 < t) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Integrable g π) : ∫ θ, pmean π t θ g ∂(Qt π t) = ∫ x, g x ∂π :=
  (pmean_Qt_aux ht hg).2

/-! ### 7. Composition of posteriors / Markov property of the channel -/

omit [IsProbabilityMeasure π] in
theorem Zt_post (t r : ℝ) (θ θ' : EuclideanSpace ℝ (Fin n)) :
    Zt (post π t θ) r θ' = Zt π (t + r) (θ + θ') / Zt π t θ := by
  unfold Zt
  rw [integral_post' t θ]
  congr 2; funext x
  rw [mul_comm, wt_add]

theorem post_post (ht : 0 < t) {r : ℝ} (hr : 0 < r) (θ θ' : EuclideanSpace ℝ (Fin n)) :
    post (post π t θ) r θ' = post π (t + r) (θ + θ') := by
  have h1 := Zt_pos (π := π) ht θ
  have h2 := Zt_pos (π := π) (add_pos ht hr) (θ + θ')
  show (post π t θ).withDensity _ = _
  rw [Zt_post, post, ← withDensity_mul _ (measurable_post_density t θ)
    (by fun_prop), post]
  congr 1; funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (div_nonneg (wt_nonneg _ _ _) h1.le), ← wt_add]
  congr 1
  field_simp

omit [IsProbabilityMeasure π] in
theorem stdGaussian_prod_map_smul {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => Real.sqrt t • p.1 + Real.sqrt r • p.2) =
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun w => Real.sqrt (t + r) • w) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have h1 : (γ.prod γ).map (fun p => Real.sqrt t • p.1 + Real.sqrt r • p.2) =
      (γ.map (fun u => Real.sqrt t • u)) ∗ (γ.map (fun u => Real.sqrt r • u)) := by
    rw [Measure.conv, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h1]
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_conv, charFun_map_smul, charFun_map_smul, charFun_map_smul, charFun_stdGaussian,
    charFun_stdGaussian, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hreal : ‖Real.sqrt t • s‖ ^ 2 + ‖Real.sqrt r • s‖ ^ 2 = ‖Real.sqrt (t + r) • s‖ ^ 2 := by
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht, Real.sq_sqrt hr,
      Real.sq_sqrt (add_nonneg ht hr)]
    ring
  have hc : ((‖Real.sqrt t • s‖ : ℂ)) ^ 2 + (‖Real.sqrt r • s‖ : ℂ) ^ 2 =
      (‖Real.sqrt (t + r) • s‖ : ℂ) ^ 2 := by exact_mod_cast hreal
  linear_combination (-1 / 2 : ℂ) * hc

omit [IsProbabilityMeasure π] in
theorem lintegral_stdGaussian_conv {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (H : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ u, ∫⁻ v, H (Real.sqrt t • u + Real.sqrt r • v) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
    ∫⁻ w, H (Real.sqrt (t + r) • w) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [← lintegral_map hH (by fun_prop : Measurable fun w : EuclideanSpace ℝ (Fin n) =>
      Real.sqrt (t + r) • w), ← stdGaussian_prod_map_smul ht hr, lintegral_map hH (by fun_prop),
    lintegral_prod _ (by fun_prop)]

theorem lintegral_Qt_post (ht : 0 < t) {r : ℝ} (hr : 0 < r)
    (F : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ θ, ∫⁻ θ', F (θ + θ') ∂(Qt (post π t θ) r) ∂(Qt π t) = ∫⁻ η, F η ∂(Qt π (t + r)) := by
  have htr : 0 < t + r := add_pos ht hr
  have hZ := measurable_Zt (π := π) ht
  have hZ' := measurable_Zt (π := π) htr
  have key : ∀ θ, ∫⁻ θ', F (θ + θ') ∂(Qt (post π t θ) r) =
      ∫⁻ v, F (θ + Real.sqrt r • v) *
        ENNReal.ofReal (Zt π (t + r) (θ + Real.sqrt r • v) / Zt π t θ)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    intro θ
    have := post_isProb (π := π) ht θ
    rw [lintegral_Qt hr _ (by fun_prop)]
    simp_rw [Zt_post]
  simp_rw [key]
  have hmeas : Measurable (fun θ => ∫⁻ v, F (θ + Real.sqrt r • v) *
        ENNReal.ofReal (Zt π (t + r) (θ + Real.sqrt r • v) / Zt π t θ)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
    Measurable.lintegral_prod_right' (f := fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) => F (p.1 + Real.sqrt r • p.2) *
        ENNReal.ofReal (Zt π (t + r) (p.1 + Real.sqrt r • p.2) / Zt π t p.1)) (by fun_prop)
  rw [lintegral_Qt ht _ hmeas, lintegral_Qt htr _ hF]
  have key2 : ∀ u : EuclideanSpace ℝ (Fin n),
      (∫⁻ v, F (Real.sqrt t • u + Real.sqrt r • v) *
        ENNReal.ofReal (Zt π (t + r) (Real.sqrt t • u + Real.sqrt r • v) / Zt π t (Real.sqrt t • u))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) * ENNReal.ofReal (Zt π t (Real.sqrt t • u)) =
      ∫⁻ v, F (Real.sqrt t • u + Real.sqrt r • v) *
        ENNReal.ofReal (Zt π (t + r) (Real.sqrt t • u + Real.sqrt r • v))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    intro u
    rw [← lintegral_mul_const _ (by fun_prop)]
    congr 1; funext v
    rw [mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (Zt_nonneg _ _) (Zt_nonneg _ _)),
      div_mul_cancel₀ _ (Zt_pos ht _).ne']
  simp_rw [key2]
  exact lintegral_stdGaussian_conv ht.le hr.le
    (fun η => F η * ENNReal.ofReal (Zt π (t + r) η)) (by fun_prop)

end PSBSL

end
end

-- ===== Engine.lean =====
section

/-!
# The heat-flow engine (integrated form)
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace PSBSL

/-! ### Gaussian density of `stdGaussian` -/

theorem eng_lintegral_fin_prod {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : ℝ × (Fin n → ℝ), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, Fin.cons_zero]
          rfl
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf _),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact Finset.aemeasurable_fun_prod _
            (fun (i : Fin n) _ => ((hf i.succ).comp (measurable_pi_apply i)).aemeasurable)
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem eng_pi_gaussianReal (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      volume.withDensity (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  refine Measure.pi_eq (μ := fun _ : Fin n => gaussianReal 0 1) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    eng_lintegral_fin_prod _ _ (fun _ => measurable_gaussianPDF 0 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ (hs i)]

theorem eng_prod_gaussianPDF (n : ℕ) (x : Fin n → ℝ) :
    ∏ i, gaussianPDF 0 1 (x i) = ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
      Real.exp (-‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 / 2)) := by
  simp only [gaussianPDF, gaussianPDFReal]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, EuclideanSpace.norm_sq_eq]
  congr 1
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity),
      ← Real.rpow_mul_natCast (by positivity)]
    congr 1
    · simp
    · ring
  · congr 1
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs, neg_div]

/-- The standard Gaussian density on `ℝⁿ`. -/
def eng_gd (n : ℕ) (g : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖g‖ ^ 2 / 2)

theorem eng_gd_pos (n : ℕ) (g : EuclideanSpace ℝ (Fin n)) : 0 < eng_gd n g := by
  unfold eng_gd; positivity

theorem eng_continuous_gd (n : ℕ) : Continuous (eng_gd n) := by
  unfold eng_gd; fun_prop

theorem eng_stdGaussian_eq (n : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) =
      volume.withDensity (fun g => ENNReal.ofReal (eng_gd n g)) := by
  rw [← map_pi_eq_stdGaussian, eng_pi_gaussianReal]
  ext s hs
  rw [Measure.map_apply (WithLp.measurable_toLp 2 _) hs,
    withDensity_apply _ (hs.preimage (WithLp.measurable_toLp 2 _)), withDensity_apply _ hs,
    ← (PiLp.volume_preserving_toLp (Fin n)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
  congr 1
  funext x
  exact eng_prod_gaussianPDF n x

theorem eng_integral_stdGaussian (n : ℕ) (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ g, h g ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = ∫ g, eng_gd n g * h g := by
  rw [eng_stdGaussian_eq]
  have hm : Measurable (fun g => (eng_gd n g).toNNReal) :=
    (eng_continuous_gd n).measurable.real_toNNReal
  change ∫ g, h g ∂(volume.withDensity (fun g => ((eng_gd n g).toNNReal : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul hm]
  congr 1; funext g
  rw [NNReal.smul_def, Real.coe_toNNReal _ (eng_gd_pos n g).le, smul_eq_mul]

theorem eng_integrable_stdGaussian_iff (n : ℕ) (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    Integrable h (stdGaussian (EuclideanSpace ℝ (Fin n))) ↔
      Integrable (fun g => eng_gd n g * h g) volume := by
  rw [eng_stdGaussian_eq]
  have hm : Measurable (fun g => (eng_gd n g).toNNReal) :=
    (eng_continuous_gd n).measurable.real_toNNReal
  change Integrable h (volume.withDensity (fun g => ((eng_gd n g).toNNReal : ℝ≥0∞))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul hm]
  apply integrable_congr
  refine Eventually.of_forall fun g => ?_
  simp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (eng_gd_pos n g).le, smul_eq_mul]

/-! ### The weight -/

section Weight

variable {n : ℕ}

theorem eng_wt_pos (s : ℝ) (θ x : EuclideanSpace ℝ (Fin n)) : 0 < wt s θ x := Real.exp_pos _

theorem eng_wt_smul (s c : ℝ) (u x : EuclideanSpace ℝ (Fin n)) :
    wt s (c • u) x = Real.exp (c * ⟪u, x⟫ - s * ‖x‖ ^ 2 / 2) := by
  unfold wt; rw [real_inner_smul_left]

theorem eng_wt_le {s : ℝ} (hs : 0 ≤ s) (u x : EuclideanSpace ℝ (Fin n)) :
    wt s (Real.sqrt s • u) x ≤ Real.exp (‖u‖ ^ 2 / 2) := by
  rw [eng_wt_smul]
  apply Real.exp_le_exp.2
  have h := norm_sub_sq_real u (Real.sqrt s • x)
  rw [real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hs] at h
  nlinarith [sq_nonneg ‖u - Real.sqrt s • x‖]

theorem eng_continuous_wt :
    Continuous (fun p : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      wt p.1.1 (Real.sqrt p.1.1 • p.1.2) p.2) := by
  unfold wt; fun_prop

theorem eng_continuous_wt' (s : ℝ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      wt s (Real.sqrt s • p.1) p.2) := by
  unfold wt; fun_prop

/-- Gaussian density times weight = shifted Gaussian density. -/
theorem eng_gd_mul_wt {s : ℝ} (hs : 0 ≤ s) (u x : EuclideanSpace ℝ (Fin n)) :
    eng_gd n u * wt s (Real.sqrt s • u) x = eng_gd n (u - Real.sqrt s • x) := by
  unfold eng_gd
  rw [eng_wt_smul, mul_assoc, ← Real.exp_add]
  congr 2
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hs]
  ring

end Weight

/-! ### Cameron–Martin -/

section CM

variable {n : ℕ}

theorem eng_cm_lintegral {s : ℝ} (hs : 0 ≤ s) (x : EuclideanSpace ℝ (Fin n))
    (h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ u, h u * ENNReal.ofReal (wt s (Real.sqrt s • u) x) ∂(stdGaussian _) =
      ∫⁻ g, h (Real.sqrt s • x + g) ∂(stdGaussian _) := by
  have hgd : Measurable (fun g : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (eng_gd n g)) :=
    (eng_continuous_gd n).measurable.ennreal_ofReal
  have hw : Measurable (fun u : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (wt s (Real.sqrt s • u) x)) :=
    ((eng_continuous_wt' s).comp (Continuous.prodMk_left x)).measurable.ennreal_ofReal
  have hhw : Measurable (fun u => h u * ENNReal.ofReal (wt s (Real.sqrt s • u) x)) := hh.mul hw
  rw [eng_stdGaussian_eq, lintegral_withDensity_eq_lintegral_mul _ hgd hhw,
    lintegral_withDensity_eq_lintegral_mul _ hgd
      (show Measurable (fun g => h (Real.sqrt s • x + g)) from hh.comp (measurable_const_add _))]
  rw [← lintegral_add_right_eq_self _ (Real.sqrt s • x)]
  congr 1; funext g
  simp only [Pi.mul_apply]
  rw [mul_comm (h _), ← mul_assoc, ← ENNReal.ofReal_mul (eng_gd_pos n _).le, eng_gd_mul_wt hs,
    add_sub_cancel_right, add_comm g]

theorem eng_cm_lintegral_prod {s : ℝ} (hs : 0 ≤ s) (π : Measure (EuclideanSpace ℝ (Fin n)))
    [SFinite π]
    (h : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ p, h p * ENNReal.ofReal (wt s (Real.sqrt s • p.1) p.2) ∂((stdGaussian _).prod π) =
      ∫⁻ q, h (Real.sqrt s • q.1 + q.2, q.1) ∂(π.prod (stdGaussian _)) := by
  have hw : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (wt s (Real.sqrt s • p.1) p.2)) :=
    (eng_continuous_wt' s).measurable.ennreal_ofReal
  have hhw : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      h p * ENNReal.ofReal (wt s (Real.sqrt s • p.1) p.2)) := hh.mul hw
  rw [lintegral_prod_symm _ hhw.aemeasurable,
    lintegral_prod _ (show Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)
      => h (Real.sqrt s • q.1 + q.2, q.1)) from hh.comp (by fun_prop)).aemeasurable]
  congr 1; funext x
  exact eng_cm_lintegral hs x (fun u => h (u, x)) (hh.comp (by fun_prop))

/-- Cameron–Martin, measure form. -/
theorem eng_cm_measure {s : ℝ} (hs : 0 ≤ s) (π : Measure (EuclideanSpace ℝ (Fin n)))
    [SFinite π] :
    ((stdGaussian _).prod π).withDensity
        (fun p => ENNReal.ofReal (wt s (Real.sqrt s • p.1) p.2)) =
      (π.prod (stdGaussian _)).map
        (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (Real.sqrt s • q.1 + q.2, q.1)) := by
  have hT : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (Real.sqrt s • q.1 + q.2, q.1)) := by fun_prop
  ext A hA
  rw [withDensity_apply _ hA, Measure.map_apply hT hA, ← lintegral_indicator hA,
    ← lintegral_indicator_one (hT hA)]
  have := eng_cm_lintegral_prod hs π (A.indicator 1) (measurable_one.indicator hA)
  convert this using 1
  · congr 1; funext p
    by_cases hp : p ∈ A <;> simp [hp]
  · congr 1

variable (π : Measure (EuclideanSpace ℝ (Fin n))) [SFinite π]

theorem eng_cm_integrable_iff {s : ℝ} (hs : 0 ≤ s)
    (F : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hF : Measurable F) :
    Integrable (fun p => F p * wt s (Real.sqrt s • p.1) p.2) ((stdGaussian _).prod π) ↔
      Integrable (fun q => F (Real.sqrt s • q.1 + q.2, q.1)) (π.prod (stdGaussian _)) := by
  have hT : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (Real.sqrt s • q.1 + q.2, q.1)) := by fun_prop
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (wt s (Real.sqrt s • p.1) p.2).toNNReal) :=
    (eng_continuous_wt' s).measurable.real_toNNReal
  have h1 : Integrable (fun p => F p * wt s (Real.sqrt s • p.1) p.2) ((stdGaussian _).prod π) ↔
      Integrable F (((stdGaussian _).prod π).withDensity
        (fun p => ENNReal.ofReal (wt s (Real.sqrt s • p.1) p.2))) := by
    change _ ↔ Integrable F (((stdGaussian _).prod π).withDensity
        (fun p => ((wt s (Real.sqrt s • p.1) p.2).toNNReal : ℝ≥0∞)))
    rw [integrable_withDensity_iff_integrable_smul hm]
    apply integrable_congr
    refine Eventually.of_forall fun p => ?_
    simp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (eng_wt_pos _ _ _).le, smul_eq_mul, mul_comm]
  rw [h1, eng_cm_measure hs π, integrable_map_measure hF.aestronglyMeasurable hT.aemeasurable]
  rfl

theorem eng_cm_integral {s : ℝ} (hs : 0 ≤ s)
    (F : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hF : Measurable F) :
    ∫ p, F p * wt s (Real.sqrt s • p.1) p.2 ∂((stdGaussian _).prod π) =
      ∫ q, F (Real.sqrt s • q.1 + q.2, q.1) ∂(π.prod (stdGaussian _)) := by
  have hT : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (Real.sqrt s • q.1 + q.2, q.1)) := by fun_prop
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (wt s (Real.sqrt s • p.1) p.2).toNNReal) :=
    (eng_continuous_wt' s).measurable.real_toNNReal
  have h1 : ∫ p, F p * wt s (Real.sqrt s • p.1) p.2 ∂((stdGaussian _).prod π) =
      ∫ p, F p ∂(((stdGaussian _).prod π).withDensity
        (fun p => ENNReal.ofReal (wt s (Real.sqrt s • p.1) p.2))) := by
    change _ = ∫ p, F p ∂(((stdGaussian _).prod π).withDensity
        (fun p => ((wt s (Real.sqrt s • p.1) p.2).toNNReal : ℝ≥0∞)))
    rw [integral_withDensity_eq_integral_smul hm]
    congr 1; funext p
    rw [NNReal.smul_def, Real.coe_toNNReal _ (eng_wt_pos _ _ _).le, smul_eq_mul, mul_comm]
  rw [h1, eng_cm_measure hs π, integral_map hT.aemeasurable hF.aestronglyMeasurable]

end CM

/-! ### Posterior formulas -/

section Post

variable {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n)))

theorem eng_continuous_wt_x (s : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : Continuous (wt s θ) := by
  unfold wt; fun_prop

theorem eng_Zt_nonneg (s : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : 0 ≤ Zt π s θ :=
  integral_nonneg fun x => (eng_wt_pos s θ x).le

theorem eng_integral_post {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (s : ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin n) → G) :
    ∫ x, h x ∂(post π s θ) = (Zt π s θ)⁻¹ • ∫ x, wt s θ x • h x ∂π := by
  have hm : Measurable (fun x => (wt s θ x / Zt π s θ).toNNReal) :=
    ((eng_continuous_wt_x s θ).measurable.div_const _).real_toNNReal
  unfold post
  change ∫ x, h x ∂(π.withDensity (fun x => ((wt s θ x / Zt π s θ).toNNReal : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul hm, ← integral_smul]
  congr 1; funext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg (eng_wt_pos s θ x).le
    (eng_Zt_nonneg π s θ)), smul_smul, div_eq_inv_mul]

theorem eng_pmean_eq (s : ℝ) (θ : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    pmean π s θ g = (∫ x, g x * wt s θ x ∂π) / Zt π s θ := by
  unfold pmean
  rw [eng_integral_post, smul_eq_mul, inv_mul_eq_div]
  congr 1; congr 1; funext x; rw [smul_eq_mul, mul_comm]

theorem eng_pcov_eq (s : ℝ) (θ : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    pcov π s θ g = (Zt π s θ)⁻¹ • ∫ x, wt s θ x • ((g x - pmean π s θ g) • x) ∂π := by
  unfold pcov
  rw [eng_integral_post]

set_option linter.unusedSectionVars false

variable [IsProbabilityMeasure π]

theorem eng_integrable_mul_wt {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n))
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : Integrable h π) :
    Integrable (fun x => h x * wt s (Real.sqrt s • u) x) π :=
  hh.mul_bdd (eng_continuous_wt_x _ _).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (eng_wt_pos _ _ _)]; exact eng_wt_le hs u x)

theorem eng_integrable_bdd_mul_wt {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Measurable g) {K : ℝ} (hK : ∀ x, |g x| ≤ K) :
    Integrable (fun x => g x * wt s (Real.sqrt s • u) x) π :=
  eng_integrable_mul_wt π hs u (Integrable.of_bound hg.aestronglyMeasurable K
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK x))

theorem eng_integrable_wt {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => wt s (Real.sqrt s • u) x) π := by
  simpa using eng_integrable_mul_wt π hs u (integrable_const (1 : ℝ))

theorem eng_Zt_pos {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n)) :
    0 < Zt π s (Real.sqrt s • u) :=
  integral_exp_pos (f := fun x => ⟪Real.sqrt s • u, x⟫ - s * ‖x‖ ^ 2 / 2)
    (eng_integrable_wt π hs u)

theorem eng_pmean_mem {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Measurable g) {a b : ℝ}
    (hab : ∀ x, g x ∈ Set.Icc a b) : pmean π s (Real.sqrt s • u) g ∈ Set.Icc a b := by
  have hK : ∀ x, |g x| ≤ |a| + |b| := fun x => by
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;>
      linarith [(hab x).1, (hab x).2]
  have hZ := eng_Zt_pos π hs u
  have hgi := eng_integrable_bdd_mul_wt π hs u hg hK
  have hw := eng_integrable_wt π hs u
  rw [eng_pmean_eq]
  unfold Zt at hZ ⊢
  constructor
  · rw [le_div_iff₀ hZ, ← integral_const_mul]
    exact integral_mono (hw.const_mul a) hgi fun x =>
      mul_le_mul_of_nonneg_right (hab x).1 (eng_wt_pos _ _ _).le
  · rw [div_le_iff₀ hZ, ← integral_const_mul]
    exact integral_mono hgi (hw.const_mul b) fun x => by
      simp only
      exact mul_le_mul_of_nonneg_right (hab x).2 (eng_wt_pos _ _ _).le

end Post

/-! ### Differentiation under `∫ dπ` -/

section Deriv

set_option linter.unusedSectionVars false

variable {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure π]

/-- Derivative in the SNR `s` (with `θ = √s • u`). -/
theorem eng_hasDerivAt_s (h1 : Integrable (fun x => ‖x‖) π)
    (h2 : Integrable (fun x => ‖x‖ ^ 2) π) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ x, |g x| ≤ K) (u : EuclideanSpace ℝ (Fin n))
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    Integrable (fun x => g x * ((⟪u, x⟫ / (2 * Real.sqrt s₀) - ‖x‖ ^ 2 / 2) *
      wt s₀ (Real.sqrt s₀ • u) x)) π ∧
    HasDerivAt (fun s => ∫ x, g x * wt s (Real.sqrt s • u) x ∂π)
      (∫ x, g x * ((⟪u, x⟫ / (2 * Real.sqrt s₀) - ‖x‖ ^ 2 / 2) *
        wt s₀ (Real.sqrt s₀ • u) x) ∂π) s₀ := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  have hsn : Set.Ioi (s₀ / 2) ∈ 𝓝 s₀ := Ioi_mem_nhds (by linarith)
  have hc : 0 < Real.sqrt (s₀ / 2) := Real.sqrt_pos.2 (by linarith)
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun s x => g x * ((⟪u, x⟫ / (2 * Real.sqrt s) - ‖x‖ ^ 2 / 2) *
      wt s (Real.sqrt s • u) x))
    (bound := fun x => (K * Real.exp (‖u‖ ^ 2 / 2)) *
      (‖u‖ / (2 * Real.sqrt (s₀ / 2)) * ‖x‖ + ‖x‖ ^ 2 / 2)) hsn ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s =>
      (hg.mul (eng_continuous_wt_x _ _).measurable).aestronglyMeasurable
  · exact eng_integrable_bdd_mul_wt π hs₀.le u hg hK
  · exact (hg.mul (Continuous.measurable (by unfold wt; fun_prop))).aestronglyMeasurable
  · refine Eventually.of_forall fun x s hs => ?_
    have hs' : s₀ / 2 < s := hs
    have hspos : 0 < s := by linarith
    have hsq : Real.sqrt (s₀ / 2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs'.le
    have hsqpos : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
    have hw := eng_wt_le hspos.le u x
    have hwp := eng_wt_pos s (Real.sqrt s • u) x
    have hin : |⟪u, x⟫| ≤ ‖u‖ * ‖x‖ := abs_real_inner_le_norm u x
    have h3 : |⟪u, x⟫ / (2 * Real.sqrt s) - ‖x‖ ^ 2 / 2| ≤
        ‖u‖ / (2 * Real.sqrt (s₀ / 2)) * ‖x‖ + ‖x‖ ^ 2 / 2 := by
      refine (abs_sub _ _).trans ?_
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt s),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖x‖ ^ 2 / 2)]
      gcongr
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ ‖u‖ * ‖x‖ := by positivity
      calc |⟪u, x⟫| * (2 * Real.sqrt (s₀ / 2)) ≤ (‖u‖ * ‖x‖) * (2 * Real.sqrt s) := by
            gcongr
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hwp]
    calc |g x| * (|⟪u, x⟫ / (2 * Real.sqrt s) - ‖x‖ ^ 2 / 2| * wt s (Real.sqrt s • u) x)
        ≤ K * ((‖u‖ / (2 * Real.sqrt (s₀ / 2)) * ‖x‖ + ‖x‖ ^ 2 / 2) *
          Real.exp (‖u‖ ^ 2 / 2)) := by
          gcongr
          · exact hK x
      _ = _ := by ring
  · exact ((h1.const_mul _).add (h2.div_const 2)).const_mul _
  · refine Eventually.of_forall fun x s hs => ?_
    have hs' : s₀ / 2 < s := hs
    have hspos : 0 < s := by linarith
    have hsqpos : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
    have hd : HasDerivAt (fun s => Real.sqrt s * ⟪u, x⟫ - s * ‖x‖ ^ 2 / 2)
        (1 / (2 * Real.sqrt s) * ⟪u, x⟫ - 1 * ‖x‖ ^ 2 / 2) s :=
      ((Real.hasDerivAt_sqrt hspos.ne').mul_const _).sub
        (((hasDerivAt_id s).mul_const _).div_const 2)
    have := (hd.exp).const_mul (g x)
    have hfun : (fun s => g x * wt s (Real.sqrt s • u) x) =
        fun y => g x * Real.exp (Real.sqrt y * ⟪u, x⟫ - y * ‖x‖ ^ 2 / 2) := by
      funext y; rw [eng_wt_smul]
    rw [hfun]
    refine this.congr_deriv ?_
    rw [eng_wt_smul]; field_simp

/-- Derivative in the direction `v` of the natural parameter `u` (with `θ = √s • u`). -/
theorem eng_hasDerivAt_dir (h1 : Integrable (fun x => ‖x‖) π) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ x, |g x| ≤ K) {s : ℝ} (hs : 0 ≤ s)
    (u v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => g x * (Real.sqrt s * ⟪v, x⟫ * wt s (Real.sqrt s • u) x)) π ∧
    HasDerivAt (fun τ : ℝ => ∫ x, g x * wt s (Real.sqrt s • (u + τ • v)) x ∂π)
      (∫ x, g x * (Real.sqrt s * ⟪v, x⟫ * wt s (Real.sqrt s • u) x) ∂π) 0 := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  have hsn : Metric.ball (0:ℝ) 1 ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds _ one_pos
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ x => g x * wt s (Real.sqrt s • (u + τ • v)) x)
    (F' := fun τ x => g x * (Real.sqrt s * ⟪v, x⟫ * wt s (Real.sqrt s • (u + τ • v)) x))
    (bound := fun x => (K * Real.sqrt s * ‖v‖ * Real.exp ((‖u‖ + ‖v‖) ^ 2 / 2)) * ‖x‖)
    (μ := π) hsn ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [zero_smul, add_zero] at key
    exact key
  · exact Eventually.of_forall fun τ =>
      (hg.mul (eng_continuous_wt_x _ _).measurable).aestronglyMeasurable
  · exact eng_integrable_bdd_mul_wt π hs _ hg hK
  · exact (hg.mul (Continuous.measurable (by unfold wt; fun_prop))).aestronglyMeasurable
  · refine Eventually.of_forall fun x τ hτ => ?_
    have hτ' : |τ| < 1 := by simpa [Real.dist_eq] using hτ
    have hn : ‖u + τ • v‖ ≤ ‖u‖ + ‖v‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      have : |τ| * ‖v‖ ≤ 1 * ‖v‖ := by gcongr
      linarith
    have hw : wt s (Real.sqrt s • (u + τ • v)) x ≤ Real.exp ((‖u‖ + ‖v‖) ^ 2 / 2) :=
      (eng_wt_le hs _ x).trans (Real.exp_le_exp.2 (by gcongr))
    have hwp := eng_wt_pos s (Real.sqrt s • (u + τ • v)) x
    have hin : |⟪v, x⟫| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hwp,
      abs_of_nonneg (Real.sqrt_nonneg s)]
    calc |g x| * (Real.sqrt s * |⟪v, x⟫| * wt s (Real.sqrt s • (u + τ • v)) x)
        ≤ K * (Real.sqrt s * (‖v‖ * ‖x‖) * Real.exp ((‖u‖ + ‖v‖) ^ 2 / 2)) := by
          gcongr
          · exact hK x
      _ = _ := by ring
  · exact h1.const_mul _
  · refine Eventually.of_forall fun x τ _ => ?_
    have hd : HasDerivAt (fun τ : ℝ => Real.sqrt s * ⟪u, x⟫ + Real.sqrt s * τ * ⟪v, x⟫
        - s * ‖x‖ ^ 2 / 2) (Real.sqrt s * 1 * ⟪v, x⟫) τ :=
      ((((hasDerivAt_id τ).const_mul (Real.sqrt s)).mul_const ⟪v, x⟫).const_add _).sub_const _
    have := (hd.exp).const_mul (g x)
    have hfun : (fun τ : ℝ => g x * wt s (Real.sqrt s • (u + τ • v)) x) =
        fun τ => g x * Real.exp (Real.sqrt s * ⟪u, x⟫ + Real.sqrt s * τ * ⟪v, x⟫
          - s * ‖x‖ ^ 2 / 2) := by
      funext τ; rw [eng_wt_smul, inner_add_left, real_inner_smul_left]; ring_nf
    rw [hfun]
    refine this.congr_deriv ?_
    rw [eng_wt_smul, inner_add_left, real_inner_smul_left]; ring_nf

end Deriv

/-! ### Measurability of posterior quantities -/

section Meas

variable {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n))) [SFinite π]

theorem eng_measurable_Zt :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) => Zt π p.1 (Real.sqrt p.1 • p.2)) := by
  unfold Zt
  exact (eng_continuous_wt.measurable.stronglyMeasurable.integral_prod_right' (ν := π)).measurable

theorem eng_measurable_pmean {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      pmean π p.1 (Real.sqrt p.1 • p.2) f) := by
  simp_rw [eng_pmean_eq]
  refine Measurable.div ?_ (eng_measurable_Zt π)
  have : Measurable (fun q : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      f q.2 * wt q.1.1 (Real.sqrt q.1.1 • q.1.2) q.2) :=
    (hf.comp measurable_snd).mul eng_continuous_wt.measurable
  exact (this.stronglyMeasurable.integral_prod_right' (ν := π)).measurable

theorem eng_measurable_pcov {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      pcov π p.1 (Real.sqrt p.1 • p.2) f) := by
  simp_rw [eng_pcov_eq]
  refine Measurable.smul (eng_measurable_Zt π).inv ?_
  have : Measurable (fun q : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      wt q.1.1 (Real.sqrt q.1.1 • q.1.2) q.2 •
        ((f q.2 - pmean π q.1.1 (Real.sqrt q.1.1 • q.1.2) f) • q.2)) :=
    eng_continuous_wt.measurable.smul
      (((hf.comp measurable_snd).sub ((eng_measurable_pmean π hf).comp measurable_fst)).smul
        measurable_snd)
  exact (this.stronglyMeasurable.integral_prod_right' (ν := π)).measurable

end Meas

/-! ### Line derivative of the posterior mean -/

section LineDeriv

set_option linter.unusedSectionVars false

variable {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure π]

theorem eng_hasDerivAt_pmean_dir (h1 : Integrable (fun x => ‖x‖) π)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K)
    {s : ℝ} (hs : 0 ≤ s) (u v : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun τ : ℝ => pmean π s (Real.sqrt s • (u + τ • v)) f)
      (Real.sqrt s * ⟪pcov π s (Real.sqrt s • u) f, v⟫) 0 := by
  obtain ⟨hNi, hN⟩ := eng_hasDerivAt_dir π h1 hf hK hs u v
  obtain ⟨hZi, hZ⟩ := eng_hasDerivAt_dir π h1 (g := fun _ => (1:ℝ)) measurable_const
    (K := 1) (fun _ => by simp) hs u v
  simp only [one_mul] at hZi hZ
  have hZ0 : (∫ x, wt s (Real.sqrt s • (u + (0:ℝ) • v)) x ∂π) = Zt π s (Real.sqrt s • u) := by
    simp [Zt]
  have hZpos := eng_Zt_pos π hs u
  have hdiv := hN.div hZ (by rw [hZ0]; exact hZpos.ne')
  have hfun : (fun τ : ℝ => pmean π s (Real.sqrt s • (u + τ • v)) f) =
      fun τ => (∫ x, f x * wt s (Real.sqrt s • (u + τ • v)) x ∂π) /
        ∫ x, wt s (Real.sqrt s • (u + τ • v)) x ∂π := by
    funext τ; rw [eng_pmean_eq]; rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  simp only [zero_smul, add_zero]
  -- algebra
  set Z := Zt π s (Real.sqrt s • u) with hZdef
  set N := ∫ x, f x * wt s (Real.sqrt s • u) x ∂π with hNdef
  set m := pmean π s (Real.sqrt s • u) f with hmdef
  have hm : m = N / Z := by rw [hmdef, eng_pmean_eq]
  have hZ' : (∫ x, wt s (Real.sqrt s • u) x ∂π) = Z := rfl
  rw [hZ']
  have hVi : Integrable (fun x => wt s (Real.sqrt s • u) x • ((f x - m) • x)) π := by
    refine Integrable.mono' ((h1.const_mul (K + |m|)).mul_const (Real.exp (‖u‖ ^ 2 / 2)))
      ((eng_continuous_wt_x _ _).measurable.smul
        ((hf.sub measurable_const).smul measurable_id)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (eng_wt_pos _ _ _)]
    have h3 : |f x - m| ≤ K + |m| := (abs_sub _ _).trans (by linarith [hK x])
    have h4 := eng_wt_le hs u x
    calc wt s (Real.sqrt s • u) x * (|f x - m| * ‖x‖)
        ≤ Real.exp (‖u‖ ^ 2 / 2) * ((K + |m|) * ‖x‖) := by gcongr
      _ = _ := by ring
  have hinner : ⟪pcov π s (Real.sqrt s • u) f, v⟫ =
      Z⁻¹ * ∫ x, wt s (Real.sqrt s • u) x * ((f x - m) * ⟪x, v⟫) ∂π := by
    rw [eng_pcov_eq, real_inner_smul_left, real_inner_comm, ← integral_inner hVi]
    congr 2; funext x
    rw [real_inner_comm, real_inner_smul_left, real_inner_smul_left]
  have hlin : Real.sqrt s * ∫ x, wt s (Real.sqrt s • u) x * ((f x - m) * ⟪x, v⟫) ∂π =
      (∫ x, f x * (Real.sqrt s * ⟪v, x⟫ * wt s (Real.sqrt s • u) x) ∂π) -
        m * ∫ x, Real.sqrt s * ⟪v, x⟫ * wt s (Real.sqrt s • u) x ∂π := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub hNi (hZi.const_mul m)]
    congr 1; funext x
    rw [real_inner_comm]; ring
  rw [hinner, ← mul_assoc, mul_comm (Real.sqrt s) Z⁻¹, mul_assoc, hlin, hm]
  generalize (∫ x, f x * (Real.sqrt s * ⟪v, x⟫ * wt s (Real.sqrt s • u) x) ∂π) = A
  generalize (∫ x, Real.sqrt s * ⟪v, x⟫ * wt s (Real.sqrt s • u) x ∂π) = B
  field_simp

end LineDeriv

/-! ### Gaussian integration by parts -/

section GaussIBP

variable {n : ℕ}

theorem eng_gd_hasLineDerivAt (g v : EuclideanSpace ℝ (Fin n)) :
    HasLineDerivAt ℝ (eng_gd n) (-(⟪g, v⟫) * eng_gd n g) g v := by
  unfold HasLineDerivAt
  have h0 : HasDerivAt (fun t : ℝ => g + t • v) ((1:ℝ) • v) 0 :=
    ((hasDerivAt_id (0:ℝ)).smul_const v).const_add g
  have h1 := ((h0.norm_sq.neg.div_const 2).exp).const_mul ((2 * Real.pi) ^ (-(n : ℝ) / 2))
  unfold eng_gd
  refine h1.congr_deriv ?_
  simp only [zero_smul, add_zero, one_smul, Pi.neg_apply]
  ring_nf

/-- Gaussian integration by parts in a direction `v`. -/
theorem eng_gauss_ibp (v : EuclideanSpace ℝ (Fin n)) {F F' : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ∀ g, HasLineDerivAt ℝ F (F' g) g v)
    (hFi : Integrable F (stdGaussian _)) (hF'i : Integrable F' (stdGaussian _))
    (hvF : Integrable (fun g => ⟪g, v⟫ * F g) (stdGaussian _)) :
    ∫ g, ⟪g, v⟫ * F g ∂(stdGaussian _) = ∫ g, F' g ∂(stdGaussian _) := by
  rw [eng_integrable_stdGaussian_iff] at hFi hF'i hvF
  rw [eng_integral_stdGaussian, eng_integral_stdGaussian]
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (f := eng_gd n) (f' := fun g => -(⟪g, v⟫) * eng_gd n g) (g := F) (g' := F')
    (v := v) (B := ContinuousLinearMap.mul ℝ ℝ) ?_ ?_ ?_
    (fun g _ => eng_gd_hasLineDerivAt g v) (fun g _ => hF g)
  · simp only [ContinuousLinearMap.mul_apply'] at key
    rw [key, ← integral_neg]
    congr 1; funext g; ring
  · simp only [ContinuousLinearMap.mul_apply']
    refine hvF.neg.congr (Eventually.of_forall fun g => ?_)
    simp only [Pi.neg_apply]; ring
  · simpa only [ContinuousLinearMap.mul_apply'] using hF'i
  · simpa only [ContinuousLinearMap.mul_apply'] using hFi

end GaussIBP

/-! ### The core objects -/

section CoreDefs

variable {n : ℕ}

/-- posterior mean of `f` along the natural parametrisation `θ = √s • u` -/
def eng_m (π : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : ℝ)
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  pmean π s (Real.sqrt s • u) f

/-- `Ψ₀(m) + Ψ₁(m) (f x - m)` -/
def eng_H (π : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ψ₀ Ψ₁ : ℝ → ℝ) (s : ℝ) (u x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Ψ₀ (eng_m π f s u) + Ψ₁ (eng_m π f s u) * (f x - eng_m π f s u)

/-- the `s`-derivative of `Λ_u(s) = Z Ψ₀(m)` -/
def eng_L (π : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ψ₀ Ψ₁ : ℝ → ℝ) (s : ℝ) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x, (⟪u, x⟫ / (2 * Real.sqrt s) - ‖x‖ ^ 2 / 2) * eng_H π f Ψ₀ Ψ₁ s u x *
    wt s (Real.sqrt s • u) x ∂π

end CoreDefs

section Core

set_option linter.unusedSectionVars false

variable {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure π]
  (h1 : Integrable (fun x => ‖x‖) π) (h2 : Integrable (fun x => ‖x‖ ^ 2) π)
  {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {a b : ℝ}
  (hab : ∀ x, f x ∈ Set.Icc a b)
  {Ψ₀ Ψ₁ Ψ₂ : ℝ → ℝ} (hc₀ : Continuous Ψ₀) (hc₁ : Continuous Ψ₁) (hc₂ : Continuous Ψ₂)
  {K : ℝ} (hK₀ : ∀ y, |Ψ₀ y| ≤ K) (hK₁ : ∀ y, |Ψ₁ y| ≤ K) (hK₂ : ∀ y, |Ψ₂ y| ≤ K)
  (hd₀ : ∀ y ∈ Set.Icc a b, HasDerivAt Ψ₀ (Ψ₁ y) y)
  (hd₁ : ∀ y ∈ Set.Icc a b, HasDerivAt Ψ₁ (Ψ₂ y) y)

local notation "γ" => stdGaussian (EuclideanSpace ℝ (Fin n))

include hab in
theorem eng_f_bound (x : EuclideanSpace ℝ (Fin n)) : |f x| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;>
    linarith [(hab x).1, (hab x).2]

include hf hab in
theorem eng_m_mem {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n)) :
    eng_m π f s u ∈ Set.Icc a b :=
  eng_pmean_mem π hs u hf hab

include hf hab hK₀ hK₁ in
theorem eng_H_bound {s : ℝ} (hs : 0 ≤ s) (u x : EuclideanSpace ℝ (Fin n)) :
    |eng_H π f Ψ₀ Ψ₁ s u x| ≤ K * (1 + (b - a)) := by
  have hm := eng_m_mem π hf hab hs u
  have h3 : |f x - eng_m π f s u| ≤ b - a := by
    rw [abs_le]; constructor <;> linarith [hm.1, hm.2, (hab x).1, (hab x).2]
  unfold eng_H
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hK₀ 0)
  calc |Ψ₀ (eng_m π f s u)| + |Ψ₁ (eng_m π f s u)| * |f x - eng_m π f s u|
      ≤ K + K * (b - a) := by gcongr; exact hK₀ _; exact hK₁ _
    _ = _ := by ring

include hf in
theorem eng_measurable_m :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) => eng_m π f p.1 p.2) :=
  eng_measurable_pmean π hf

include hf hc₀ hc₁ in
theorem eng_measurable_H :
    Measurable (fun q : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      eng_H π f Ψ₀ Ψ₁ q.1.1 q.1.2 q.2) := by
  unfold eng_H
  have hm : Measurable (fun q : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      eng_m π f q.1.1 q.1.2) := (eng_measurable_m π hf).comp measurable_fst
  exact (hc₀.measurable.comp hm).add ((hc₁.measurable.comp hm).mul
    ((hf.comp measurable_snd).sub hm))

include hf hc₀ hc₁ in
theorem eng_measurable_H_s (s : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      eng_H π f Ψ₀ Ψ₁ s p.1 p.2) := by
  unfold eng_H
  have hm0 : Measurable (fun u : EuclideanSpace ℝ (Fin n) => eng_m π f s u) := by
    have := (eng_measurable_m π hf).comp (measurable_prodMk_left (m := inferInstance) (x := s))
    exact this
  have hm : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      eng_m π f s q.1) := hm0.comp measurable_fst
  exact (hc₀.measurable.comp hm).add ((hc₁.measurable.comp hm).mul
    ((hf.comp measurable_snd).sub hm))

include hf hc₀ hc₁ in
theorem eng_measurable_L :
    Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) => eng_L π f Ψ₀ Ψ₁ p.1 p.2) := by
  unfold eng_L
  have : Measurable (fun q : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      (⟪q.1.2, q.2⟫ / (2 * Real.sqrt q.1.1) - ‖q.2‖ ^ 2 / 2) * eng_H π f Ψ₀ Ψ₁ q.1.1 q.1.2 q.2 *
        wt q.1.1 (Real.sqrt q.1.1 • q.1.2) q.2) := by
    refine Measurable.mul (Measurable.mul ?_ (eng_measurable_H π hf hc₀ hc₁))
      eng_continuous_wt.measurable
    fun_prop
  exact (this.stronglyMeasurable.integral_prod_right' (ν := π)).measurable

/-- The integrand `F` (before the Cameron–Martin shift) whose `π`-integral against the weight
is `eng_L`. -/
theorem eng_CM_L_shift {s : ℝ} (hs : 0 < s) (x g : EuclideanSpace ℝ (Fin n)) :
    ⟪Real.sqrt s • x + g, x⟫ / (2 * Real.sqrt s) - ‖x‖ ^ 2 / 2 = ⟪g, x⟫ / (2 * Real.sqrt s) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp
  ring

include h1 hf hab hc₀ hc₁ hK₀ hK₁ in
theorem eng_L_integrable_shift {s : ℝ} (hs : 0 < s) :
    Integrable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (⟪Real.sqrt s • q.1 + q.2, q.1⟫ / (2 * Real.sqrt s) - ‖q.1‖ ^ 2 / 2) *
        eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • q.1 + q.2) q.1) (π.prod γ) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hG : Integrable (fun g : EuclideanSpace ℝ (Fin n) => ‖g‖) γ :=
    (IsGaussian.integrable_id (μ := γ)).norm
  refine Integrable.mono' ((h1.mul_prod hG).const_mul (K * (1 + (b - a)) / (2 * Real.sqrt s)))
    ?_ ?_
  · have hT : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (Real.sqrt s • q.1 + q.2, q.1)) := by fun_prop
    have hA : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ⟪Real.sqrt s • q.1 + q.2, q.1⟫ / (2 * Real.sqrt s) - ‖q.1‖ ^ 2 / 2) := by fun_prop
    have hB : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • q.1 + q.2) q.1) := by
      have := (eng_measurable_H_s π hf hc₀ hc₁ s).comp hT
      exact this
    exact (hA.mul hB).aestronglyMeasurable
  · refine Eventually.of_forall fun q => ?_
    rw [eng_CM_L_shift hs, Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt s)]
    have hH := eng_H_bound π hf hab hK₀ hK₁ hs.le (Real.sqrt s • q.1 + q.2) q.1
    have hin : |⟪q.2, q.1⟫| ≤ ‖q.1‖ * ‖q.2‖ := by
      rw [mul_comm]; exact abs_real_inner_le_norm _ _
    calc |⟪q.2, q.1⟫| / (2 * Real.sqrt s) * |eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • q.1 + q.2) q.1|
        ≤ (‖q.1‖ * ‖q.2‖) / (2 * Real.sqrt s) * (K * (1 + (b - a))) := by gcongr
      _ = _ := by ring

include h1 hf hab hc₀ hc₁ hK₀ hK₁ in
theorem eng_L_integrable_prod {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (⟪p.1, p.2⟫ / (2 * Real.sqrt s) - ‖p.2‖ ^ 2 / 2) * eng_H π f Ψ₀ Ψ₁ s p.1 p.2 *
        wt s (Real.sqrt s • p.1) p.2) (Measure.prod γ π) := by
  have hA : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪p.1, p.2⟫ / (2 * Real.sqrt s) - ‖p.2‖ ^ 2 / 2) := by fun_prop
  have := (eng_cm_integrable_iff π hs.le
    (fun p => (⟪p.1, p.2⟫ / (2 * Real.sqrt s) - ‖p.2‖ ^ 2 / 2) * eng_H π f Ψ₀ Ψ₁ s p.1 p.2)
    (hA.mul (eng_measurable_H_s π hf hc₀ hc₁ s))).2
    (eng_L_integrable_shift π h1 hf hab hc₀ hc₁ hK₀ hK₁ hs)
  exact this

include h1 hf hab hc₀ hc₁ hK₀ hK₁ in
theorem eng_L_integrable {s : ℝ} (hs : 0 < s) : Integrable (eng_L π f Ψ₀ Ψ₁ s) γ :=
  (eng_L_integrable_prod π h1 hf hab hc₀ hc₁ hK₀ hK₁ hs).integral_prod_left

include h1 hf hab hc₀ hc₁ hK₀ hK₁ in
theorem eng_integral_L_eq {s : ℝ} (hs : 0 < s) :
    ∫ u, eng_L π f Ψ₀ Ψ₁ s u ∂γ =
      ∫ q, (⟪Real.sqrt s • q.1 + q.2, q.1⟫ / (2 * Real.sqrt s) - ‖q.1‖ ^ 2 / 2) *
        eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • q.1 + q.2) q.1 ∂(π.prod γ) := by
  have hA : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪p.1, p.2⟫ / (2 * Real.sqrt s) - ‖p.2‖ ^ 2 / 2) := by fun_prop
  unfold eng_L
  rw [← integral_prod _ (eng_L_integrable_prod π h1 hf hab hc₀ hc₁ hK₀ hK₁ hs)]
  exact eng_cm_integral π hs.le
    (fun p => (⟪p.1, p.2⟫ / (2 * Real.sqrt s) - ‖p.2‖ ^ 2 / 2) * eng_H π f Ψ₀ Ψ₁ s p.1 p.2)
    (hA.mul (eng_measurable_H_s π hf hc₀ hc₁ s))

include h1 hf hab hd₀ hd₁ in
theorem eng_H_lineDeriv {s : ℝ} (hs : 0 ≤ s) (u v x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun τ : ℝ => eng_H π f Ψ₀ Ψ₁ s (u + τ • v) x)
      (Ψ₂ (eng_m π f s u) * (f x - eng_m π f s u) *
        (Real.sqrt s * ⟪pcov π s (Real.sqrt s • u) f, v⟫)) 0 := by
  have hm := eng_hasDerivAt_pmean_dir π h1 hf (eng_f_bound hab) hs u v
  set mτ : ℝ → ℝ := fun τ => pmean π s (Real.sqrt s • (u + τ • v)) f with hmτ
  have h0 : mτ 0 = eng_m π f s u := by simp [hmτ, eng_m]
  have hmem := eng_m_mem π hf hab hs u
  have hΨ₀ : HasDerivAt Ψ₀ (Ψ₁ (mτ 0)) (mτ 0) := by rw [h0]; exact hd₀ _ hmem
  have hΨ₁ : HasDerivAt Ψ₁ (Ψ₂ (mτ 0)) (mτ 0) := by rw [h0]; exact hd₁ _ hmem
  have key := (hΨ₀.comp (0:ℝ) hm).add ((hΨ₁.comp (0:ℝ) hm).mul (hm.const_sub (f x)))
  have hfun : (fun τ : ℝ => eng_H π f Ψ₀ Ψ₁ s (u + τ • v) x) =
      (fun τ => (Ψ₀ ∘ mτ) τ + (Ψ₁ ∘ mτ) τ * (f x - mτ τ)) := by
    funext τ; rfl
  rw [hfun]
  refine key.congr_deriv ?_
  simp only [Function.comp_apply, h0]
  ring

/-- the integrand after the IBP -/
def eng_F2 (π : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ψ₂ : ℝ → ℝ) (s : ℝ) (u x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2) * Ψ₂ (eng_m π f s u) * (f x - eng_m π f s u) *
    ⟪pcov π s (Real.sqrt s • u) f, x⟫

include hf hc₂ in
theorem eng_measurable_F2 (s : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      eng_F2 π f Ψ₂ s p.1 p.2) := by
  unfold eng_F2
  have hm0 : Measurable (fun u : EuclideanSpace ℝ (Fin n) => eng_m π f s u) := by
    have := (eng_measurable_m π hf).comp (measurable_prodMk_left (m := inferInstance) (x := s))
    exact this
  have hP0 : Measurable (fun u : EuclideanSpace ℝ (Fin n) => pcov π s (Real.sqrt s • u) f) := by
    have := (eng_measurable_pcov π hf).comp (measurable_prodMk_left (m := inferInstance) (x := s))
    exact this
  have hm : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      eng_m π f s q.1) := hm0.comp measurable_fst
  have hP : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      pcov π s (Real.sqrt s • q.1) f) := hP0.comp measurable_fst
  exact ((measurable_const.mul (hc₂.measurable.comp hm)).mul ((hf.comp measurable_snd).sub hm)).mul
    (hP.inner measurable_snd)

include h1 h2 in
theorem eng_jensen {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n)) :
    (∫ x, ‖x‖ * wt s (Real.sqrt s • u) x ∂π) ^ 2 ≤
      Zt π s (Real.sqrt s • u) * ∫ x, ‖x‖ ^ 2 * wt s (Real.sqrt s • u) x ∂π := by
  set M := ∫ x, ‖x‖ * wt s (Real.sqrt s • u) x ∂π
  set Q := ∫ x, ‖x‖ ^ 2 * wt s (Real.sqrt s • u) x ∂π
  set Z := Zt π s (Real.sqrt s • u) with hZ
  have hZpos : 0 < Z := eng_Zt_pos π hs u
  set l := M / Z
  have hMi := eng_integrable_mul_wt π hs u h1
  have hQi := eng_integrable_mul_wt π hs u h2
  have hwi := eng_integrable_wt π hs u
  have hnn : 0 ≤ ∫ x, (‖x‖ - l) ^ 2 * wt s (Real.sqrt s • u) x ∂π :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (eng_wt_pos _ _ _).le
  have hexp : ∫ x, (‖x‖ - l) ^ 2 * wt s (Real.sqrt s • u) x ∂π = Q - 2 * l * M + l ^ 2 * Z := by
    have : (fun x => (‖x‖ - l) ^ 2 * wt s (Real.sqrt s • u) x) = fun x =>
        (‖x‖ ^ 2 * wt s (Real.sqrt s • u) x - (2 * l) * (‖x‖ * wt s (Real.sqrt s • u) x)) +
          l ^ 2 * wt s (Real.sqrt s • u) x := by
      funext x; ring
    have hsub : Integrable (fun x => ‖x‖ ^ 2 * wt s (Real.sqrt s • u) x -
        (2 * l) * (‖x‖ * wt s (Real.sqrt s • u) x)) π := hQi.sub (hMi.const_mul _)
    rw [this, integral_add hsub (hwi.const_mul _),
      integral_sub hQi (hMi.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  rw [hexp] at hnn
  have : Q - 2 * l * M + l ^ 2 * Z = Q - M ^ 2 / Z := by
    simp only [l]; field_simp; ring
  rw [this, sub_nonneg, div_le_iff₀ hZpos] at hnn
  linarith

include h1 hf hab in
theorem eng_pcov_norm_le {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n)) :
    ‖pcov π s (Real.sqrt s • u) f‖ ≤
      (b - a) * (∫ x, ‖x‖ * wt s (Real.sqrt s • u) x ∂π) / Zt π s (Real.sqrt s • u) := by
  have hZpos := eng_Zt_pos π hs u
  have hm := eng_m_mem π hf hab hs u
  rw [eng_pcov_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hZpos), inv_mul_eq_div,
    ← integral_const_mul]
  gcongr
  refine norm_integral_le_of_norm_le ((eng_integrable_mul_wt π hs u h1).const_mul _)
    (Eventually.of_forall fun x => ?_)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (eng_wt_pos _ _ _)]
  have h3 : |f x - pmean π s (Real.sqrt s • u) f| ≤ b - a := by
    rw [abs_le]; constructor <;> linarith [hm.1, hm.2, (hab x).1, (hab x).2, show
      eng_m π f s u = pmean π s (Real.sqrt s • u) f from rfl]
  calc wt s (Real.sqrt s • u) x * (|f x - pmean π s (Real.sqrt s • u) f| * ‖x‖)
      ≤ wt s (Real.sqrt s • u) x * ((b - a) * ‖x‖) := by
        gcongr; exact (eng_wt_pos _ _ _).le
    _ = _ := by ring

include h1 hf hab in
theorem eng_integrable_V {s : ℝ} (hs : 0 ≤ s) (u : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    Integrable (fun x => wt s (Real.sqrt s • u) x • ((f x - c) • x)) π := by
  have hK := eng_f_bound hab (f := f)
  refine Integrable.mono' ((h1.const_mul (|a| + |b| + |c|)).mul_const (Real.exp (‖u‖ ^ 2 / 2)))
    ((eng_continuous_wt_x _ _).measurable.smul
      ((hf.sub measurable_const).smul measurable_id)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun x => ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (eng_wt_pos _ _ _)]
  have h3 : |f x - c| ≤ |a| + |b| + |c| := (abs_sub _ _).trans (by linarith [hK x])
  have h4 := eng_wt_le hs u x
  calc wt s (Real.sqrt s • u) x * (|f x - c| * ‖x‖)
      ≤ Real.exp (‖u‖ ^ 2 / 2) * ((|a| + |b| + |c|) * ‖x‖) := by gcongr
    _ = _ := by ring

include hf hab hK₂ in
theorem eng_F2_bound {s : ℝ} (hs : 0 ≤ s) (u x : EuclideanSpace ℝ (Fin n)) :
    |eng_F2 π f Ψ₂ s u x| ≤ (1 / 2 * K * (b - a) * ‖pcov π s (Real.sqrt s • u) f‖) * ‖x‖ := by
  have hm := eng_m_mem π hf hab hs u
  have h3 : |f x - eng_m π f s u| ≤ b - a := by
    rw [abs_le]; constructor <;> linarith [hm.1, hm.2, (hab x).1, (hab x).2]
  have hin := abs_real_inner_le_norm (pcov π s (Real.sqrt s • u) f) x
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hK₂ 0)
  have hba : 0 ≤ b - a := by linarith [(hab 0).1, (hab 0).2]
  unfold eng_F2
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  have e1 : 1 / 2 * |Ψ₂ (eng_m π f s u)| ≤ 1 / 2 * K := by linarith [hK₂ (eng_m π f s u)]
  have e2 := mul_le_mul e1 h3 (abs_nonneg _) (by positivity)
  have e3 := mul_le_mul e2 hin (abs_nonneg _) (mul_nonneg (by positivity) hba)
  calc 1 / 2 * |Ψ₂ (eng_m π f s u)| * |f x - eng_m π f s u| *
        |⟪pcov π s (Real.sqrt s • u) f, x⟫|
      ≤ 1 / 2 * K * (b - a) * (‖pcov π s (Real.sqrt s • u) f‖ * ‖x‖) := e3
    _ = _ := by ring

include h1 h2 hf hab hc₂ hK₂ in
theorem eng_F2_integrable_prod {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      eng_F2 π f Ψ₂ s p.1 p.2 * wt s (Real.sqrt s • p.1) p.2) (Measure.prod γ π) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hK₂ 0)
  have hba : 0 ≤ b - a := by linarith [(hab 0).1, (hab 0).2]
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      eng_F2 π f Ψ₂ s p.1 p.2 * wt s (Real.sqrt s • p.1) p.2) :=
    (eng_measurable_F2 π hf hc₂ s).mul (eng_continuous_wt' s).measurable
  have hF2i : ∀ u, Integrable (fun x => eng_F2 π f Ψ₂ s u x) π := fun u => by
    refine Integrable.mono' (h1.const_mul (1 / 2 * K * (b - a) * ‖pcov π s (Real.sqrt s • u) f‖))
      ?_ (Eventually.of_forall fun x => ?_)
    · have := (eng_measurable_F2 π hf hc₂ s).comp (measurable_prodMk_left (m := inferInstance)
        (x := u))
      exact this.aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact eng_F2_bound π hf hab hK₂ hs.le u x
  have hQ : Integrable (fun u => ∫ x, ‖x‖ ^ 2 * wt s (Real.sqrt s • u) x ∂π) γ := by
    have h2' : Integrable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖q.1‖ ^ 2) (π.prod γ) := by
      simpa using h2.mul_prod (integrable_const (1:ℝ) : Integrable (fun _ => (1:ℝ)) γ)
    have := (eng_cm_integrable_iff π hs.le (fun p => ‖p.2‖ ^ 2) (by fun_prop)).2 h2'
    exact this.integral_prod_left
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun u => eng_integrable_mul_wt π hs.le u (hF2i u), ?_⟩
  refine Integrable.mono' (hQ.const_mul (1 / 2 * K * (b - a) * (b - a)))
    hmeas.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall fun u => ?_)
  have hZpos := eng_Zt_pos π hs.le u
  have hMi := eng_integrable_mul_wt π hs.le u h1
  have hJ := eng_jensen π h1 h2 hs.le u
  have hPn := eng_pcov_norm_le π h1 hf hab hs.le u
  set M := ∫ x, ‖x‖ * wt s (Real.sqrt s • u) x ∂π
  set Q := ∫ x, ‖x‖ ^ 2 * wt s (Real.sqrt s • u) x ∂π
  set Z := Zt π s (Real.sqrt s • u)
  set P := pcov π s (Real.sqrt s • u) f
  have hM0 : 0 ≤ M := integral_nonneg fun x => mul_nonneg (norm_nonneg _) (eng_wt_pos _ _ _).le
  rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  calc ∫ x, ‖eng_F2 π f Ψ₂ s u x * wt s (Real.sqrt s • u) x‖ ∂π
      ≤ ∫ x, (1 / 2 * K * (b - a) * ‖P‖) * (‖x‖ * wt s (Real.sqrt s • u) x) ∂π := by
        refine integral_mono (eng_integrable_mul_wt π hs.le u (hF2i u)).norm
          (hMi.const_mul _) fun x => ?_
        simp only
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (eng_wt_pos _ _ _),
          ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (eng_F2_bound π hf hab hK₂ hs.le u x)
          (eng_wt_pos _ _ _).le
    _ = (1 / 2 * K * (b - a)) * (‖P‖ * M) := by rw [integral_const_mul]; ring
    _ ≤ (1 / 2 * K * (b - a)) * ((b - a) * M / Z * M) := by gcongr
    _ = (1 / 2 * K * (b - a) * (b - a)) * (M ^ 2 / Z) := by ring
    _ ≤ (1 / 2 * K * (b - a) * (b - a)) * Q := by
        gcongr
        rw [div_le_iff₀ hZpos]; linarith

include h1 hf hab in
theorem eng_F2_inner {s : ℝ} (hs : 0 < s) (u : EuclideanSpace ℝ (Fin n)) :
    ∫ x, eng_F2 π f Ψ₂ s u x * wt s (Real.sqrt s • u) x ∂π =
      1 / 2 * (Zt π s (Real.sqrt s • u) * Ψ₂ (pmean π s (Real.sqrt s • u) f) *
        ‖pcov π s (Real.sqrt s • u) f‖ ^ 2) := by
  have hZpos := eng_Zt_pos π hs.le u
  set m := pmean π s (Real.sqrt s • u) f with hm
  set Z := Zt π s (Real.sqrt s • u)
  set P := pcov π s (Real.sqrt s • u) f with hP
  have hV := eng_integrable_V π h1 hf hab hs.le u m
  have hPV : Z • P = ∫ x, wt s (Real.sqrt s • u) x • ((f x - m) • x) ∂π := by
    rw [hP, eng_pcov_eq, smul_inv_smul₀ hZpos.ne']
  have : (fun x => eng_F2 π f Ψ₂ s u x * wt s (Real.sqrt s • u) x) =
      fun x => (1 / 2 * Ψ₂ m) * ⟪P, wt s (Real.sqrt s • u) x • ((f x - m) • x)⟫ := by
    funext x
    unfold eng_F2 eng_m
    rw [real_inner_smul_right, real_inner_smul_right]
    ring
  rw [this, integral_const_mul, integral_inner hV, ← hPV, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

include h1 h2 hf hab hc₀ hc₁ hc₂ hK₀ hK₁ hK₂ hd₀ hd₁ in
/-- **Gaussian integration by parts identity** for fixed `s > 0`. -/
theorem eng_integral_L {s : ℝ} (hs : 0 < s) :
    ∫ u, eng_L π f Ψ₀ Ψ₁ s u ∂γ =
      1 / 2 * ∫ u, Zt π s (Real.sqrt s • u) * Ψ₂ (pmean π s (Real.sqrt s • u) f) *
        ‖pcov π s (Real.sqrt s • u) f‖ ^ 2 ∂γ := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hKH0 : 0 ≤ K * (1 + (b - a)) := le_trans (abs_nonneg _)
    (eng_H_bound π hf hab hK₀ hK₁ hs.le 0 0)
  have hF2m : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      eng_F2 π f Ψ₂ s p.1 p.2) := eng_measurable_F2 π hf hc₂ s
  have hF2T : Integrable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      eng_F2 π f Ψ₂ s (Real.sqrt s • q.1 + q.2) q.1) (π.prod γ) :=
    (eng_cm_integrable_iff π hs.le (fun p => eng_F2 π f Ψ₂ s p.1 p.2) hF2m).1
      (eng_F2_integrable_prod π h1 h2 hf hab hc₂ hK₂ hs)
  have hRHS : 1 / 2 * ∫ u, Zt π s (Real.sqrt s • u) * Ψ₂ (pmean π s (Real.sqrt s • u) f) *
        ‖pcov π s (Real.sqrt s • u) f‖ ^ 2 ∂γ =
      ∫ q, eng_F2 π f Ψ₂ s (Real.sqrt s • q.1 + q.2) q.1 ∂(π.prod γ) := by
    rw [← eng_cm_integral π hs.le (fun p => eng_F2 π f Ψ₂ s p.1 p.2) hF2m,
      integral_prod _ (eng_F2_integrable_prod π h1 h2 hf hab hc₂ hK₂ hs), ← integral_const_mul]
    congr 1; funext u
    rw [eng_F2_inner π h1 hf hab hs u]
  rw [eng_integral_L_eq π h1 hf hab hc₀ hc₁ hK₀ hK₁ hs, hRHS,
    integral_prod _ (eng_L_integrable_shift π h1 hf hab hc₀ hc₁ hK₀ hK₁ hs),
    integral_prod _ hF2T]
  apply integral_congr_ae
  filter_upwards [hF2T.prod_right_ae] with x hx
  simp only at hx ⊢
  have e1 : ∀ g : EuclideanSpace ℝ (Fin n),
      (⟪Real.sqrt s • x + g, x⟫ / (2 * Real.sqrt s) - ‖x‖ ^ 2 / 2) *
        eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • x + g) x =
      (1 / (2 * Real.sqrt s)) * (⟪g, x⟫ * eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • x + g) x) := by
    intro g; rw [eng_CM_L_shift hs]; ring
  have e2 : ∀ g : EuclideanSpace ℝ (Fin n),
      eng_F2 π f Ψ₂ s (Real.sqrt s • x + g) x =
      (1 / (2 * Real.sqrt s)) * (Ψ₂ (eng_m π f s (Real.sqrt s • x + g)) *
        (f x - eng_m π f s (Real.sqrt s • x + g)) *
        (Real.sqrt s * ⟪pcov π s (Real.sqrt s • (Real.sqrt s • x + g)) f, x⟫)) := by
    intro g; unfold eng_F2; field_simp
  simp_rw [e1, e2, integral_const_mul]
  congr 1
  have hTx : Measurable (fun g : EuclideanSpace ℝ (Fin n) => (Real.sqrt s • x + g, x)) := by
    fun_prop
  have hHm : Measurable (fun g : EuclideanSpace ℝ (Fin n) =>
      eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • x + g) x) := by
    have := (eng_measurable_H_s π hf hc₀ hc₁ s).comp hTx
    exact this
  refine eng_gauss_ibp x ?_ ?_ ?_ ?_
  · intro g
    unfold HasLineDerivAt
    have := eng_H_lineDeriv π h1 hf hab hd₀ hd₁ hs.le (Real.sqrt s • x + g) x x
    have hfun : (fun t : ℝ => eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • x + (g + t • x)) x) =
        fun t => eng_H π f Ψ₀ Ψ₁ s ((Real.sqrt s • x + g) + t • x) x := by
      funext t; rw [add_assoc]
    rw [hfun]
    exact this
  · exact Integrable.of_bound hHm.aestronglyMeasurable (K * (1 + (b - a)))
      (Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs]; exact eng_H_bound π hf hab hK₀ hK₁ hs.le _ _)
  · refine (hx.const_mul (2 * Real.sqrt s)).congr (Eventually.of_forall fun g => ?_)
    simp only
    rw [e2]; field_simp
  · refine Integrable.mono' (((IsGaussian.integrable_id (μ := γ)).norm).mul_const
      (‖x‖ * (K * (1 + (b - a))))) ((measurable_id.inner measurable_const).mul hHm).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := eng_H_bound π hf hab hK₀ hK₁ hs.le (Real.sqrt s • x + g) x
    have hin := abs_real_inner_le_norm g x
    calc |⟪g, x⟫| * |eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • x + g) x|
        ≤ (‖g‖ * ‖x‖) * (K * (1 + (b - a))) := by gcongr
      _ = _ := by simp only [id]; ring

include h1 h2 hf hab hd₀ in
/-- The `s`-derivative of `Λ_u(s) = Z Ψ₀(m)`. -/
theorem eng_hasDerivAt_Lambda {s₀ : ℝ} (hs₀ : 0 < s₀) (u : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => Zt π s (Real.sqrt s • u) * Ψ₀ (pmean π s (Real.sqrt s • u) f))
      (eng_L π f Ψ₀ Ψ₁ s₀ u) s₀ := by
  obtain ⟨hZi, hZ⟩ := eng_hasDerivAt_s π h1 h2 (g := fun _ => (1:ℝ)) measurable_const
    (K := 1) (fun _ => by simp) u hs₀
  simp only [one_mul] at hZi hZ
  obtain ⟨hNi, hN⟩ := eng_hasDerivAt_s π h1 h2 hf (eng_f_bound hab) u hs₀
  have hZpos := eng_Zt_pos π hs₀.le u
  have hfun : (fun s => Zt π s (Real.sqrt s • u) * Ψ₀ (pmean π s (Real.sqrt s • u) f)) =
      fun s => (∫ x, wt s (Real.sqrt s • u) x ∂π) *
        Ψ₀ ((∫ x, f x * wt s (Real.sqrt s • u) x ∂π) / ∫ x, wt s (Real.sqrt s • u) x ∂π) := by
    funext s; rw [eng_pmean_eq]; rfl
  have hm := hN.div hZ hZpos.ne'
  have hmeq : (∫ x, f x * wt s₀ (Real.sqrt s₀ • u) x ∂π) / (∫ x, wt s₀ (Real.sqrt s₀ • u) x ∂π)
      = eng_m π f s₀ u := by
    unfold eng_m; rw [eng_pmean_eq]; rfl
  have hmem := eng_m_mem π hf hab hs₀.le u
  rw [← hmeq] at hmem
  have hΨ := (hd₀ _ hmem).comp s₀ hm
  have key := hZ.mul hΨ
  rw [hfun]
  refine key.congr_deriv ?_
  -- compute `eng_L`
  set c : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ⟪u, x⟫ / (2 * Real.sqrt s₀) - ‖x‖ ^ 2 / 2
    with hc
  set m := eng_m π f s₀ u with hmdef
  have hL : eng_L π f Ψ₀ Ψ₁ s₀ u =
      Ψ₀ m * (∫ x, c x * wt s₀ (Real.sqrt s₀ • u) x ∂π) +
        Ψ₁ m * ((∫ x, f x * (c x * wt s₀ (Real.sqrt s₀ • u) x) ∂π) -
          m * ∫ x, c x * wt s₀ (Real.sqrt s₀ • u) x ∂π) := by
    unfold eng_L eng_H
    rw [← hmdef]
    have : (fun x => (⟪u, x⟫ / (2 * Real.sqrt s₀) - ‖x‖ ^ 2 / 2) * (Ψ₀ m + Ψ₁ m * (f x - m)) *
        wt s₀ (Real.sqrt s₀ • u) x) = fun x =>
        (Ψ₀ m * (c x * wt s₀ (Real.sqrt s₀ • u) x) +
          Ψ₁ m * (f x * (c x * wt s₀ (Real.sqrt s₀ • u) x))) -
          (Ψ₁ m * m) * (c x * wt s₀ (Real.sqrt s₀ • u) x) := by
      funext x; simp only [hc]; ring
    have hadd : Integrable (fun x => Ψ₀ m * (c x * wt s₀ (Real.sqrt s₀ • u) x) +
        Ψ₁ m * (f x * (c x * wt s₀ (Real.sqrt s₀ • u) x))) π :=
      (hZi.const_mul _).add (hNi.const_mul _)
    rw [this, integral_sub hadd (hZi.const_mul _), integral_add (hZi.const_mul _)
      (hNi.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
    ring
  rw [hL, ← hmeq]
  simp only [Function.comp_apply, Pi.div_apply]
  generalize (∫ x, c x * wt s₀ (Real.sqrt s₀ • u) x ∂π) = Z'
  generalize (∫ x, f x * (c x * wt s₀ (Real.sqrt s₀ • u) x) ∂π) = N'
  have hZne : (∫ x, wt s₀ (Real.sqrt s₀ • u) x ∂π) ≠ 0 := hZpos.ne'
  generalize (∫ x, wt s₀ (Real.sqrt s₀ • u) x ∂π) = Z at hZne ⊢
  generalize (∫ x, f x * wt s₀ (Real.sqrt s₀ • u) x ∂π) = N
  field_simp

include hf hab hK₀ hK₁ in
theorem eng_shift_bound {s : ℝ} (hs : 0 < s)
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    ‖(⟪Real.sqrt s • q.1 + q.2, q.1⟫ / (2 * Real.sqrt s) - ‖q.1‖ ^ 2 / 2) *
        eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • q.1 + q.2) q.1‖ ≤
      K * (1 + (b - a)) / (2 * Real.sqrt s) * (‖q.1‖ * ‖q.2‖) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  rw [eng_CM_L_shift hs, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt s)]
  have hH := eng_H_bound π hf hab hK₀ hK₁ hs.le (Real.sqrt s • q.1 + q.2) q.1
  have hin : |⟪q.2, q.1⟫| ≤ ‖q.1‖ * ‖q.2‖ := by
    rw [mul_comm]; exact abs_real_inner_le_norm _ _
  calc |⟪q.2, q.1⟫| / (2 * Real.sqrt s) * |eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • q.1 + q.2) q.1|
      ≤ (‖q.1‖ * ‖q.2‖) / (2 * Real.sqrt s) * (K * (1 + (b - a))) := by gcongr
    _ = _ := by ring

include h1 hf hab hc₀ hc₁ hK₀ hK₁ in
theorem eng_integral_norm_L_le {s : ℝ} (hs : 0 < s) :
    ∫ u, ‖eng_L π f Ψ₀ Ψ₁ s u‖ ∂γ ≤
      K * (1 + (b - a)) / (2 * Real.sqrt s) * ((∫ x, ‖x‖ ∂π) * ∫ g, ‖g‖ ∂γ) := by
  have hG : Integrable (fun g : EuclideanSpace ℝ (Fin n) => ‖g‖) γ :=
    (IsGaussian.integrable_id (μ := γ)).norm
  have hFw := eng_L_integrable_prod π h1 hf hab hc₀ hc₁ hK₀ hK₁ hs
  have hA : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪p.1, p.2⟫ / (2 * Real.sqrt s) - ‖p.2‖ ^ 2 / 2) := by fun_prop
  have hFm : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖(⟪p.1, p.2⟫ / (2 * Real.sqrt s) - ‖p.2‖ ^ 2 / 2) * eng_H π f Ψ₀ Ψ₁ s p.1 p.2‖) :=
    (hA.mul (eng_measurable_H_s π hf hc₀ hc₁ s)).norm
  calc ∫ u, ‖eng_L π f Ψ₀ Ψ₁ s u‖ ∂γ
      ≤ ∫ u, ∫ x, ‖(⟪u, x⟫ / (2 * Real.sqrt s) - ‖x‖ ^ 2 / 2) * eng_H π f Ψ₀ Ψ₁ s u x *
          wt s (Real.sqrt s • u) x‖ ∂π ∂γ := by
        refine integral_mono (eng_L_integrable π h1 hf hab hc₀ hc₁ hK₀ hK₁ hs).norm
          hFw.integral_norm_prod_left fun u => ?_
        exact norm_integral_le_integral_norm _
    _ = ∫ p, ‖(⟪p.1, p.2⟫ / (2 * Real.sqrt s) - ‖p.2‖ ^ 2 / 2) * eng_H π f Ψ₀ Ψ₁ s p.1 p.2‖ *
          wt s (Real.sqrt s • p.1) p.2 ∂(Measure.prod γ π) := by
        rw [← integral_prod _ hFw.norm]
        congr 1; funext p
        rw [norm_mul, Real.norm_of_nonneg (eng_wt_pos _ _ _).le]
    _ = ∫ q, ‖(⟪Real.sqrt s • q.1 + q.2, q.1⟫ / (2 * Real.sqrt s) - ‖q.1‖ ^ 2 / 2) *
          eng_H π f Ψ₀ Ψ₁ s (Real.sqrt s • q.1 + q.2) q.1‖ ∂(π.prod γ) :=
        eng_cm_integral π hs.le _ hFm
    _ ≤ ∫ q, K * (1 + (b - a)) / (2 * Real.sqrt s) * (‖q.1‖ * ‖q.2‖) ∂(π.prod γ) :=
        integral_mono (eng_L_integrable_shift π h1 hf hab hc₀ hc₁ hK₀ hK₁ hs).norm
          ((h1.mul_prod hG).const_mul _) fun q => eng_shift_bound π hf hab hK₀ hK₁ hs q
    _ = _ := by rw [integral_const_mul, integral_prod_mul]

include h1 hf hab hc₀ hc₁ hK₀ hK₁ in
theorem eng_L_integrable_interval {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    Integrable (Function.uncurry fun s u => eng_L π f Ψ₀ Ψ₁ s u)
      ((volume.restrict (Set.uIoc t₁ t₂)).prod γ) := by
  rw [Set.uIoc_of_le h12]
  have hm : Measurable (Function.uncurry fun s u => eng_L π f Ψ₀ Ψ₁ s u) :=
    eng_measurable_L π hf hc₀ hc₁
  have hK : 0 ≤ K * (1 + (b - a)) := le_trans (abs_nonneg _)
    (eng_H_bound π hf hab hK₀ hK₁ le_rfl 0 0)
  have hsq1 : 0 < Real.sqrt t₁ := Real.sqrt_pos.2 ht₁
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs =>
      eng_L_integrable π h1 hf hab hc₀ hc₁ hK₀ hK₁ (ht₁.trans hs.1)
  · refine Integrable.mono' (integrable_const
      (K * (1 + (b - a)) / (2 * Real.sqrt t₁) * ((∫ x, ‖x‖ ∂π) * ∫ g, ‖g‖ ∂γ)))
      hm.aestronglyMeasurable.norm.integral_prod_right' ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun s hs => ?_
    have hspos : 0 < s := ht₁.trans hs.1
    have hsq : Real.sqrt t₁ ≤ Real.sqrt s := Real.sqrt_le_sqrt hs.1.le
    rw [Real.norm_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
    refine (eng_integral_norm_L_le π h1 hf hab hc₀ hc₁ hK₀ hK₁ hspos).trans ?_
    have hI : 0 ≤ (∫ x, ‖x‖ ∂π) * ∫ g, ‖g‖ ∂γ :=
      mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
    gcongr

include hf hab hc₀ hK₀ in
theorem eng_Lambda_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun u => Zt π t (Real.sqrt t • u) * Ψ₀ (pmean π t (Real.sqrt t • u) f)) γ := by
  have hm0 : Measurable (fun u : EuclideanSpace ℝ (Fin n) => eng_m π f t u) := by
    have := (eng_measurable_m π hf).comp (measurable_prodMk_left (m := inferInstance) (x := t))
    exact this
  have hF : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      Ψ₀ (eng_m π f t p.1)) := hc₀.measurable.comp (hm0.comp measurable_fst)
  have hT : Measurable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      Ψ₀ (eng_m π f t (Real.sqrt t • q.1 + q.2))) := by
    have := hF.comp (show Measurable (fun q : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) => (Real.sqrt t • q.1 + q.2, q.1)) by fun_prop)
    exact this
  have hFT : Integrable (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      Ψ₀ (eng_m π f t (Real.sqrt t • q.1 + q.2))) (π.prod γ) :=
    Integrable.of_bound hT.aestronglyMeasurable K
      (Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hK₀ _)
  have := ((eng_cm_integrable_iff π ht.le (fun p => Ψ₀ (eng_m π f t p.1)) hF).2 hFT
    ).integral_prod_left
  refine this.congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [integral_const_mul]
  unfold Zt eng_m
  ring

include h1 h2 hf hab hc₀ hc₁ hc₂ hK₀ hK₁ hK₂ hd₀ hd₁ in
/-- The engine with globally continuous, bounded `Ψ₀, Ψ₁, Ψ₂`. -/
theorem eng_engine_core {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    ∫ u, Zt π t₂ (Real.sqrt t₂ • u) * Ψ₀ (pmean π t₂ (Real.sqrt t₂ • u) f) ∂γ -
      ∫ u, Zt π t₁ (Real.sqrt t₁ • u) * Ψ₀ (pmean π t₁ (Real.sqrt t₁ • u) f) ∂γ =
    ∫ s in t₁..t₂, (1 / 2) * ∫ u, Zt π s (Real.sqrt s • u) *
      Ψ₂ (pmean π s (Real.sqrt s • u) f) * ‖pcov π s (Real.sqrt s • u) f‖ ^ 2 ∂γ := by
  have ht₂ : 0 < t₂ := ht₁.trans_le h12
  have hint := eng_L_integrable_interval π h1 hf hab hc₀ hc₁ hK₀ hK₁ ht₁ h12
  rw [← integral_sub (eng_Lambda_integrable π hf hab hc₀ hK₀ ht₂)
    (eng_Lambda_integrable π hf hab hc₀ hK₀ ht₁)]
  have hstep : ∫ u, (Zt π t₂ (Real.sqrt t₂ • u) * Ψ₀ (pmean π t₂ (Real.sqrt t₂ • u) f) -
      Zt π t₁ (Real.sqrt t₁ • u) * Ψ₀ (pmean π t₁ (Real.sqrt t₁ • u) f)) ∂γ =
      ∫ u, (∫ s in t₁..t₂, eng_L π f Ψ₀ Ψ₁ s u) ∂γ := by
    apply integral_congr_ae
    filter_upwards [hint.prod_left_ae] with u hu
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s hs
      rw [Set.uIcc_of_le h12] at hs
      exact eng_hasDerivAt_Lambda π h1 h2 hf hab hd₀ (ht₁.trans_le hs.1) u
    · rw [intervalIntegrable_iff, Set.uIoc_of_le h12]
      rw [Set.uIoc_of_le h12] at hu
      exact hu
  rw [hstep, ← intervalIntegral_integral_swap hint]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le h12] at hs
  exact eng_integral_L π h1 h2 hf hab hc₀ hc₁ hc₂ hK₀ hK₁ hK₂ hd₀ hd₁ (ht₁.trans_le hs.1)

end Core

/-! ### From `Φ ∈ C²(J)` to globally continuous bounded `Ψ₀, Ψ₁, Ψ₂` -/

section Reduction

theorem eng_le_one_add_pow_four (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ 4 := by
  rcases le_total r 1 with h | h
  · nlinarith [pow_nonneg hr 4]
  · nlinarith [mul_le_mul h h zero_le_one hr, pow_nonneg hr 2, mul_nonneg hr hr]

theorem eng_sq_le_one_add_pow_four (r : ℝ) : r ^ 2 ≤ 1 + r ^ 4 := by
  nlinarith [sq_nonneg (r ^ 2 - 1 / 2)]

/-- clamping to `[a', b']` -/
def eng_clamp (a' b' : ℝ) (y : ℝ) : ℝ := max a' (min b' y)

theorem eng_continuous_clamp (a' b' : ℝ) : Continuous (eng_clamp a' b') := by
  unfold eng_clamp; fun_prop

theorem eng_clamp_mem {a' b' : ℝ} (h : a' ≤ b') (y : ℝ) : eng_clamp a' b' y ∈ Set.Icc a' b' :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem eng_clamp_of_mem {a' b' y : ℝ} (hy : y ∈ Set.Icc a' b') : eng_clamp a' b' y = y := by
  unfold eng_clamp; rw [min_eq_right hy.2, max_eq_right hy.1]

theorem eng_clamp_eventuallyEq {a' b' y : ℝ} (hy : y ∈ Set.Ioo a' b') :
    eng_clamp a' b' =ᶠ[𝓝 y] id :=
  Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hy) fun _ hz =>
    eng_clamp_of_mem (Set.Ioo_subset_Icc_self hz)

end Reduction

/-- **The heat-flow engine** (integrated form): with
`Λ t u = Zt π t (√t • u) * Φ (pmean π t (√t • u) f)`,
`∫ Λ t₂ dγ - ∫ Λ t₁ dγ = ∫_{t₁}^{t₂} (1/2) ∫ Z Φ''(m) ‖pcov‖² dγ ds`. -/
theorem engine_phi {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure π]
    (hmom : Integrable (fun x => ‖x‖ ^ 4) π) {J : Set ℝ} (hJ : IsOpen J) {Φ : ℝ → ℝ}
    (hΦ : ContDiffOn ℝ 2 Φ J) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : ∀ x, f x ∈ Set.Icc a b) (habJ : Set.Icc a b ⊆ J)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    ∫ u, Zt π t₂ (Real.sqrt t₂ • u) * Φ (pmean π t₂ (Real.sqrt t₂ • u) f)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) -
      ∫ u, Zt π t₁ (Real.sqrt t₁ • u) * Φ (pmean π t₁ (Real.sqrt t₁ • u) f)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
    ∫ s in t₁..t₂, (1 / 2) * ∫ u, Zt π s (Real.sqrt s • u) *
      deriv (deriv Φ) (pmean π s (Real.sqrt s • u) f) * ‖pcov π s (Real.sqrt s • u) f‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  -- moments
  have h1 : Integrable (fun x => ‖x‖) π :=
    Integrable.mono' ((integrable_const (1:ℝ)).add hmom) continuous_norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact eng_le_one_add_pow_four _ (norm_nonneg _))
  have h2 : Integrable (fun x => ‖x‖ ^ 2) π :=
    Integrable.mono' ((integrable_const (1:ℝ)).add hmom)
      (continuous_norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact eng_sq_le_one_add_pow_four _)
  -- the interval
  have hab' : a ≤ b := (hab 0).1.trans (hab 0).2
  obtain ⟨δ, hδ, hδJ⟩ := (isCompact_Icc (a := a) (b := b)).exists_cthickening_subset_open hJ habJ
  set a' := a - δ
  set b' := b + δ
  have hIJ : Set.Icc a' b' ⊆ J := by
    intro y hy
    apply hδJ
    refine Metric.mem_cthickening_of_dist_le y (eng_clamp a b y) δ _ (eng_clamp_mem hab' y) ?_
    rw [Real.dist_eq]
    unfold eng_clamp
    rw [abs_le]
    constructor
    · rcases le_total b y with h | h
      · rw [min_eq_left h, max_eq_right hab']; linarith [hy.2]
      · rw [min_eq_right h]
        rcases le_total a y with h' | h'
        · rw [max_eq_right h']; linarith
        · rw [max_eq_left h']; linarith [hy.1]
    · rcases le_total b y with h | h
      · rw [min_eq_left h, max_eq_right hab']; linarith [hy.2]
      · rw [min_eq_right h]
        rcases le_total a y with h' | h'
        · rw [max_eq_right h']; linarith
        · rw [max_eq_left h']; linarith [hy.1]
  have hab'' : a' ≤ b' := by simp only [a', b']; linarith
  have hIoo : Set.Icc a b ⊆ Set.Ioo a' b' := fun y hy =>
    ⟨by simp only [a']; linarith [hy.1], by simp only [b']; linarith [hy.2]⟩
  -- derivatives of Φ
  have hΦ' := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hJ).1 (by exact hΦ)
  have hΦ'' := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hJ).1 (by exact hΦ'.2.2)
  have hD₀ : ∀ y ∈ J, HasDerivAt Φ (deriv Φ y) y := fun y hy =>
    ((hΦ'.1 y hy).differentiableAt (hJ.mem_nhds hy)).hasDerivAt
  have hD₁ : ∀ y ∈ J, HasDerivAt (deriv Φ) (deriv (deriv Φ) y) y := fun y hy =>
    ((hΦ''.1 y hy).differentiableAt (hJ.mem_nhds hy)).hasDerivAt
  have hC₀ : ContinuousOn Φ J := hΦ.continuousOn
  have hC₁ : ContinuousOn (deriv Φ) J := hΦ'.2.2.continuousOn
  have hC₂ : ContinuousOn (deriv (deriv Φ)) J := hΦ''.2.2.continuousOn
  -- the clamped functions
  set c := eng_clamp a' b'
  have hcc : Continuous c := eng_continuous_clamp a' b'
  have hcm : ∀ y, c y ∈ Set.Icc a' b' := eng_clamp_mem hab''
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g J → Continuous (g ∘ c) := fun g hg =>
    (hg.mono hIJ).comp_continuous hcc hcm
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hC₀.mono hIJ)
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hC₁.mono hIJ)
  obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hC₂.mono hIJ)
  set K := max K₀ (max K₁ K₂)
  have hB : ∀ g : ℝ → ℝ, ∀ C : ℝ, (∀ y ∈ Set.Icc a' b', ‖g y‖ ≤ C) → C ≤ K →
      ∀ y, |(g ∘ c) y| ≤ K := fun g C hC hCK y => by
    rw [← Real.norm_eq_abs]; exact (hC _ (hcm y)).trans hCK
  have hcid : ∀ y ∈ Set.Icc a b, c y = y := fun y hy =>
    eng_clamp_of_mem (Set.Ioo_subset_Icc_self (hIoo hy))
  have hdd : ∀ (g g' : ℝ → ℝ), (∀ y ∈ J, HasDerivAt g (g' y) y) →
      ∀ y ∈ Set.Icc a b, HasDerivAt (g ∘ c) ((g' ∘ c) y) y := by
    intro g g' hg y hy
    have hyJ : y ∈ J := habJ hy
    have hev : g ∘ c =ᶠ[𝓝 y] g := by
      filter_upwards [eng_clamp_eventuallyEq (hIoo hy)] with z hz
      exact congrArg g hz
    rw [Function.comp_apply, hcid y hy]
    exact (hg y hyJ).congr_of_eventuallyEq hev
  have core := eng_engine_core π h1 h2 hf hab (hcont _ hC₀) (hcont _ hC₁) (hcont _ hC₂)
    (hB _ _ hK₀ (le_max_left _ _))
    (hB _ _ hK₁ ((le_max_left _ _).trans (le_max_right _ _)))
    (hB _ _ hK₂ ((le_max_right _ _).trans (le_max_right _ _)))
    (hdd _ _ hD₀) (hdd _ _ hD₁) ht₁ h12
  have hpm : ∀ s, 0 < s → ∀ u, c (pmean π s (Real.sqrt s • u) f) = pmean π s (Real.sqrt s • u) f :=
    fun s hs u => hcid _ (eng_pmean_mem π hs.le u hf hab)
  have ht₂ : 0 < t₂ := ht₁.trans_le h12
  simp only [Function.comp_apply, hpm t₂ ht₂, hpm t₁ ht₁] at core
  rw [core]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le h12] at hs
  simp only [hpm s (ht₁.trans_le hs.1)]

/-- `Λ t u = Zt π t (√t • u) * Φ (pmean π t (√t • u) f)` -/
def engLambda {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n))) (Φ : ℝ → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Zt π t (Real.sqrt t • u) * Φ (pmean π t (Real.sqrt t • u) f)

/-- `engine_phi` stated with `engLambda`. -/
theorem engine_phi_Lambda {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure π]
    (hmom : Integrable (fun x => ‖x‖ ^ 4) π) {J : Set ℝ} (hJ : IsOpen J) {Φ : ℝ → ℝ}
    (hΦ : ContDiffOn ℝ 2 Φ J) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : ∀ x, f x ∈ Set.Icc a b) (habJ : Set.Icc a b ⊆ J)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    ∫ u, engLambda π Φ f t₂ u ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) -
      ∫ u, engLambda π Φ f t₁ u ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
    ∫ s in t₁..t₂, (1 / 2) * ∫ u, Zt π s (Real.sqrt s • u) *
      deriv (deriv Φ) (pmean π s (Real.sqrt s • u) f) * ‖pcov π s (Real.sqrt s • u) f‖ ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) :=
  engine_phi π hmom hJ hΦ hf hab habJ ht₁ h12

end PSBSL

end
end

-- ===== Limits.lean =====
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace PSBSL

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "γₙ" => stdGaussian (EuclideanSpace ℝ (Fin n))

variable {π : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure π] {t : ℝ}

/-! ### (J) Joint tower property -/

theorem measurable_lintegral_post_joint (ht : 0 < t) {G : Eₙ × Eₙ → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun θ => ∫⁻ x, G (θ, x) ∂(post π t θ)) := by
  have hZ := measurable_Zt (π := π) ht
  have : (fun θ => ∫⁻ x, G (θ, x) ∂(post π t θ)) =
      fun θ => ∫⁻ x, ENNReal.ofReal (wt t θ x / Zt π t θ) * G (θ, x) ∂π := by
    funext θ
    exact lintegral_post_eq t θ (g := fun x => G (θ, x)) (by fun_prop)
  rw [this]
  exact Measurable.lintegral_prod_right' (f := fun p : Eₙ × Eₙ =>
    ENNReal.ofReal (wt t p.1 p.2 / Zt π t p.1) * G p) (by fun_prop)

theorem lintegral_post_Qt_joint (ht : 0 < t) {G : Eₙ × Eₙ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ θ, ∫⁻ x, G (θ, x) ∂(post π t θ) ∂(Qt π t) =
      ∫⁻ x, ∫⁻ g, G (t • x + Real.sqrt t • g, x) ∂γₙ ∂π := by
  have hZ := measurable_Zt (π := π) ht
  rw [lintegral_Qt ht _ (measurable_lintegral_post_joint ht hG)]
  have key : ∀ u : Eₙ,
      (∫⁻ x, G (Real.sqrt t • u, x) ∂(post π t (Real.sqrt t • u))) *
        ENNReal.ofReal (Zt π t (Real.sqrt t • u)) =
      ∫⁻ x, G (Real.sqrt t • u, x) * ENNReal.ofReal (wt t (Real.sqrt t • u) x) ∂π := by
    intro u
    rw [lintegral_post_eq t _ (g := fun x => G (Real.sqrt t • u, x)) (by fun_prop),
      ← lintegral_mul_const _ (by fun_prop)]
    congr 1; funext x
    rw [mul_comm _ (G _), mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (wt_nonneg _ _ _)
      (Zt_nonneg _ _)), div_mul_cancel₀ _ (Zt_pos ht _).ne']
  simp_rw [key]
  rw [lintegral_lintegral_swap (by fun_prop)]
  congr 1; funext x
  have := lintegral_stdGaussian_add (fun u => G (Real.sqrt t • u, x)) (by fun_prop)
    (Real.sqrt t • x)
  simp only [smul_add, smul_smul, Real.mul_self_sqrt ht.le] at this
  rw [this]
  congr 1; funext u
  congr 2
  unfold wt
  rw [inner_smul_left, inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt ht.le, real_inner_comm]

private theorem joint_aux_nonneg (ht : 0 < t) {H : Eₙ × Eₙ → ℝ} (hH : Measurable H)
    (hH0 : ∀ p, 0 ≤ H p)
    (hint : Integrable (fun p : Eₙ × Eₙ => H (t • p.1 + Real.sqrt t • p.2, p.1)) (π.prod γₙ)) :
    (∀ᵐ θ ∂(Qt π t), Integrable (fun x => H (θ, x)) (post π t θ)) ∧
    Integrable (fun θ => ∫ x, H (θ, x) ∂(post π t θ)) (Qt π t) ∧
    ∫ θ, ∫ x, H (θ, x) ∂(post π t θ) ∂(Qt π t) =
      ∫ p, H (t • p.1 + Real.sqrt t • p.2, p.1) ∂(π.prod γₙ) := by
  have hQ := isProb_Qt (π := π) t
  set I : Eₙ → ℝ≥0∞ := fun θ => ∫⁻ x, ENNReal.ofReal (H (θ, x)) ∂(post π t θ) with hI
  have hIm : Measurable I := measurable_lintegral_post_joint ht (G := fun p => ENNReal.ofReal (H p))
    (by fun_prop)
  have hlin : ∫⁻ θ, I θ ∂(Qt π t) =
      ∫⁻ p, ENNReal.ofReal (H (t • p.1 + Real.sqrt t • p.2, p.1)) ∂(π.prod γₙ) := by
    rw [hI, lintegral_post_Qt_joint ht (G := fun p => ENNReal.ofReal (H p)) (by fun_prop),
      lintegral_prod _ (by fun_prop)]
  have hfin : ∫⁻ θ, I θ ∂(Qt π t) < ∞ := by
    rw [hlin]
    have := hint.lintegral_lt_top
    convert this using 1
  have hae : ∀ᵐ θ ∂(Qt π t), I θ < ∞ := ae_lt_top hIm hfin.ne
  have hsec : ∀ θ, Measurable (fun x => H (θ, x)) := fun θ =>
    hH.comp (measurable_const.prodMk measurable_id)
  have heq : ∀ θ, ∫ x, H (θ, x) ∂(post π t θ) = (I θ).toReal := fun θ =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => hH0 _)
      (hsec θ).aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hae] with θ hθ
    refine ⟨(hsec θ).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => hH0 _)]
    exact hθ
  · simp_rw [heq]
    refine ⟨hIm.ennreal_toReal.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun θ => ENNReal.toReal_nonneg)]
    exact lt_of_le_of_lt (lintegral_mono fun θ => ENNReal.ofReal_toReal_le) hfin
  · simp_rw [heq]
    rw [integral_toReal hIm.aemeasurable hae, hlin,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun p => hH0 _) hint.1]

/-- Joint tower property, Bochner version. -/
theorem integral_post_Qt_joint' (ht : 0 < t) {G : Eₙ × Eₙ → ℝ} (hG : Measurable G)
    (hint : Integrable (fun p : Eₙ × Eₙ => G (t • p.1 + Real.sqrt t • p.2, p.1)) (π.prod γₙ)) :
    ∫ θ, ∫ x, G (θ, x) ∂(post π t θ) ∂(Qt π t) =
      ∫ p, G (t • p.1 + Real.sqrt t • p.2, p.1) ∂(π.prod γₙ) := by
  obtain ⟨a1, b1, c1⟩ := joint_aux_nonneg (π := π) ht (H := fun p => max (G p) 0) (by fun_prop)
    (fun p => le_max_right _ _) hint.pos_part
  obtain ⟨a2, b2, c2⟩ := joint_aux_nonneg (π := π) ht (H := fun p => max (-G p) 0) (by fun_prop)
    (fun p => le_max_right _ _) hint.neg_part
  have e1 : (fun θ => ∫ x, G (θ, x) ∂(post π t θ)) =ᵐ[Qt π t]
      fun θ => ∫ x, max (G (θ, x)) 0 ∂(post π t θ) - ∫ x, max (-G (θ, x)) 0 ∂(post π t θ) := by
    filter_upwards [a1, a2] with θ h1 h2
    rw [← integral_sub h1 h2]
    simp only [max_zero_sub_max_neg_zero_eq_self]
  rw [integral_congr_ae e1, integral_sub b1 b2, c1, c2, ← integral_sub hint.pos_part hint.neg_part]
  simp only [max_zero_sub_max_neg_zero_eq_self]

/-- Joint tower property, Bochner version with an iterated right-hand side. -/
theorem integral_post_Qt_joint (ht : 0 < t) {G : Eₙ × Eₙ → ℝ} (hG : Measurable G)
    (hint : Integrable (fun p : Eₙ × Eₙ => G (t • p.1 + Real.sqrt t • p.2, p.1)) (π.prod γₙ)) :
    ∫ θ, ∫ x, G (θ, x) ∂(post π t θ) ∂(Qt π t) =
      ∫ x, ∫ g, G (t • x + Real.sqrt t • g, x) ∂γₙ ∂π := by
  rw [integral_post_Qt_joint' ht hG hint, integral_prod _ hint]

/-- Joint tower property for bounded measurable `G`. -/
theorem integral_post_Qt_joint_of_bounded (ht : 0 < t) {G : Eₙ × Eₙ → ℝ} (hG : Measurable G)
    {C : ℝ} (hC : ∀ p, |G p| ≤ C) :
    ∫ θ, ∫ x, G (θ, x) ∂(post π t θ) ∂(Qt π t) =
      ∫ x, ∫ g, G (t • x + Real.sqrt t • g, x) ∂γₙ ∂π := by
  refine integral_post_Qt_joint ht hG (Integrable.of_bound
    (hG.comp (by fun_prop : Measurable fun p : Eₙ × Eₙ =>
      (t • p.1 + Real.sqrt t • p.2, p.1))).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => ?_))
  rw [Real.norm_eq_abs]; exact hC _

/-! ### Auxiliary real-analysis facts -/

theorem taylor2_bound {Φ : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J) (hΦ : ContDiffOn ℝ 2 Φ J)
    {a b : ℝ} (hab : Set.Icc a b ⊆ J) :
    ∃ M, 0 ≤ M ∧ ∀ z ∈ Set.Icc a b, ∀ m ∈ Set.Icc a b,
      |Φ z - Φ m - deriv Φ m * (z - m)| ≤ M * (z - m) ^ 2 := by
  obtain ⟨hd1, -, h1⟩ := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hJ).1 hΦ
  obtain ⟨hd2, -, h2⟩ := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hJ).1 h1
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn (h2.continuousOn.mono hab)
  refine ⟨max M0 0, le_max_right _ _, fun z hz m hm => ?_⟩
  set M := max M0 0
  have hdiff1 : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ Φ x := fun x hx =>
    hd1.differentiableAt (hJ.mem_nhds (hab hx))
  have hdiff2 : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (deriv Φ) x := fun x hx =>
    hd2.differentiableAt (hJ.mem_nhds (hab hx))
  -- Lipschitz bound for `Φ'`
  have hlip : ∀ s ∈ Set.Icc a b, |deriv Φ s - deriv Φ m| ≤ M * |s - m| := by
    intro s hs
    have := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le (C := M) hdiff2
      (fun x hx => (hM0 x hx).trans (le_max_left M0 0)) hm hs
    simpa [Real.norm_eq_abs] using this
  have hseg : Set.uIcc m z ⊆ Set.Icc a b := Set.uIcc_subset_Icc hm hz
  have key := (convex_uIcc m z).norm_image_sub_le_of_norm_deriv_le
    (f := fun s => Φ s - deriv Φ m * s) (C := M * |z - m|)
    (fun x hx => ((hdiff1 x (hseg hx)).sub ((differentiableAt_id).const_mul _)))
    (fun x hx => by
      have hd : HasDerivAt (fun s => Φ s - deriv Φ m * s) (deriv Φ x - deriv Φ m * 1) x :=
        (hdiff1 x (hseg hx)).hasDerivAt.sub ((hasDerivAt_id' x).const_mul (deriv Φ m))
      rw [hd.deriv, mul_one, Real.norm_eq_abs]
      refine (hlip x (hseg hx)).trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
      rcases le_total m z with h | h
      · rw [Set.uIcc_of_le h] at hx
        rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith)]; linarith [hx.2]
      · rw [Set.uIcc_of_ge h] at hx
        rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos (by linarith)]; linarith [hx.1])
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  simp only [Real.norm_eq_abs] at key
  calc |Φ z - Φ m - deriv Φ m * (z - m)| = |Φ z - deriv Φ m * z - (Φ m - deriv Φ m * m)| := by
        ring_nf
    _ ≤ M * |z - m| * |z - m| := key
    _ = M * (z - m) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

theorem integral_mem_Icc' {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hfm : Measurable f) {a b : ℝ} (hfab : ∀ y, f y ∈ Set.Icc a b) :
    ∫ y, f y ∂μ ∈ Set.Icc a b := by
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable (max |a| |b|)
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_le_max_abs_abs (hfab y).1 (hfab y).2)
  constructor
  · have := integral_mono (integrable_const a) hfi (fun y => (hfab y).1)
    simpa using this
  · have := integral_mono hfi (integrable_const b) (fun y => (hfab y).2)
    simpa using this

theorem integral_sq_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hfm : Measurable f) {a b : ℝ} (hfab : ∀ y, f y ∈ Set.Icc a b) (c : ℝ) :
    ∫ y, (f y - ∫ z, f z ∂μ) ^ 2 ∂μ ≤ ∫ y, (f y - c) ^ 2 ∂μ := by
  have hb : ∀ y, |f y| ≤ max |a| |b| := fun y => abs_le_max_abs_abs (hfab y).1 (hfab y).2
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable (max |a| |b|)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb y)
  set m := ∫ z, f z ∂μ
  have hsq : ∀ d : ℝ, Integrable (fun y => (f y - d) ^ 2) μ := fun d => by
    have : (fun y => (f y - d) ^ 2) = fun y => f y * f y - 2 * d * f y + d ^ 2 := by
      funext y; ring
    rw [this]
    exact ((hfi.bdd_mul (c := max |a| |b|) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb y)).sub
      (hfi.const_mul _)).add (integrable_const _)
  have key : ∫ y, (f y - c) ^ 2 ∂μ - ∫ y, (f y - m) ^ 2 ∂μ = (m - c) ^ 2 := by
    rw [← integral_sub (hsq c) (hsq m)]
    have : (fun y => (f y - c) ^ 2 - (f y - m) ^ 2) =
        fun y => 2 * (m - c) * f y - (m ^ 2 - c ^ 2) := by funext y; ring
    rw [this, integral_sub (hfi.const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  nlinarith [sq_nonneg (m - c)]

theorem bregman_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {Φ : ℝ → ℝ} {a b M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ Set.Icc a b, ∀ m ∈ Set.Icc a b, |Φ z - Φ m - deriv Φ m * (z - m)| ≤ M * (z - m) ^ 2)
    {f : α → ℝ} (hfm : Measurable f) (hfab : ∀ y, f y ∈ Set.Icc a b)
    (hΦi : Integrable (fun y => Φ (f y)) μ) (c : ℝ) :
    |∫ y, Φ (f y) ∂μ - Φ (∫ y, f y ∂μ)| ≤ M * ∫ y, (f y - c) ^ 2 ∂μ := by
  have hb : ∀ y, |f y| ≤ max |a| |b| := fun y => abs_le_max_abs_abs (hfab y).1 (hfab y).2
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable (max |a| |b|)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb y)
  set m := ∫ z, f z ∂μ with hm_def
  have hmab : m ∈ Set.Icc a b := integral_mem_Icc' hfm hfab
  have hsq : Integrable (fun y => (f y - m) ^ 2) μ := by
    have : (fun y => (f y - m) ^ 2) = fun y => f y * f y - 2 * m * f y + m ^ 2 := by
      funext y; ring
    rw [this]
    exact ((hfi.bdd_mul (c := max |a| |b|) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb y)).sub
      (hfi.const_mul _)).add (integrable_const _)
  have hlin : Integrable (fun y => Φ m + deriv Φ m * (f y - m)) μ :=
    (integrable_const _).add ((hfi.sub (integrable_const _)).const_mul _)
  have e1 : ∫ y, Φ (f y) ∂μ - Φ m =
      ∫ y, (Φ (f y) - (Φ m + deriv Φ m * (f y - m))) ∂μ := by
    have h1 : Integrable (fun y => f y - m) μ := hfi.sub (integrable_const _)
    have h2 : Integrable (fun y => deriv Φ m * (f y - m)) μ := h1.const_mul _
    have h3 : ∫ y, (Φ m + deriv Φ m * (f y - m)) ∂μ = Φ m := by
      rw [integral_add (integrable_const _) h2, integral_const_mul,
        integral_sub hfi (integrable_const _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, ← hm_def]
      ring
    rw [integral_sub hΦi hlin, h3]
  rw [e1]
  refine le_trans (abs_integral_le_integral_abs) ?_
  refine le_trans (integral_mono (hΦi.sub hlin).abs (hsq.const_mul M) fun y => ?_) ?_
  · have := hM (f y) (hfab y) m hmab
    simp only
    rw [show Φ (f y) - (Φ m + deriv Φ m * (f y - m)) = Φ (f y) - Φ m - deriv Φ m * (f y - m) by
      ring]
    exact this
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_sq_sub_le hfm hfab c) hM0

theorem integral_lintegral_norm_sq_stdGaussian_lt_top :
    ∫⁻ g, ENNReal.ofReal (‖g‖ ^ 2) ∂γₙ < ∞ :=
  ((IsGaussian.memLp_two_id (μ := γₙ)).integrable_norm_pow two_ne_zero).lintegral_lt_top

theorem norm_sub_inv_smul_obs_sq (ht : 0 < t) (x g : Eₙ) :
    ‖x - t⁻¹ • (t • x + Real.sqrt t • g)‖ ^ 2 = ‖g‖ ^ 2 / t := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, smul_smul, sub_add_cancel_left,
    norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt ht.le]
  field_simp

/-! ### (L∞) The limit `t → ∞` -/

/-- Quantitative form: `|∫ Φ(pmean) dQt - ∫ Φ(f) dπ| ≤ M L² K / t`. -/
theorem abs_Ifun_sub_le {J : Set ℝ} (hJ : IsOpen J) {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 2 Φ J)
    {a b : ℝ} (hab : Set.Icc a b ⊆ J) {f : Eₙ → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (hfab : ∀ y, f y ∈ Set.Icc a b) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t →
      ‖∫ θ, Φ (pmean π t θ f) ∂(Qt π t) - ∫ y, Φ (f y) ∂π‖ ≤ C / t := by
  obtain ⟨M, hM0, hM⟩ := taylor2_bound hJ hΦ hab
  have hle : a ≤ b := (hfab 0).1.trans (hfab 0).2
  set Φt : ℝ → ℝ := fun s => Φ (Set.projIcc a b hle s) with hΦt_def
  have hΦtc : Continuous Φt := (hΦ.continuousOn.mono hab).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun s => (Set.projIcc a b hle s).2)
  have hΦt : ∀ s ∈ Set.Icc a b, Φt s = Φ s := fun s hs => by
    simp only [hΦt_def, Set.projIcc_of_mem hle hs]
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hΦ.continuousOn.mono hab))
  have hΦtb : ∀ s, ‖Φt s‖ ≤ C0 := fun s => hC0 _ (Set.projIcc a b hle s).2
  have hfm : Measurable f := hf.continuous.measurable
  have hfb : ∀ y, ‖f y‖ ≤ max |a| |b| := fun y => by
    rw [Real.norm_eq_abs]; exact abs_le_max_abs_abs (hfab y).1 (hfab y).2
  have hfi : ∀ (μ : Measure Eₙ) [IsFiniteMeasure μ], Integrable f μ := fun μ _ =>
    Integrable.of_bound hfm.aestronglyMeasurable _ (Filter.Eventually.of_forall hfb)
  have hΦfm : Measurable (fun y => Φ (f y)) := by
    have : (fun y => Φ (f y)) = fun y => Φt (f y) := funext fun y => (hΦt _ (hfab y)).symm
    rw [this]; exact hΦtc.measurable.comp hfm
  have hΦfi : ∀ (μ : Measure Eₙ) [IsFiniteMeasure μ], Integrable (fun y => Φ (f y)) μ :=
    fun μ _ => Integrable.of_bound hΦfm.aestronglyMeasurable C0
      (Filter.Eventually.of_forall fun y => by rw [← hΦt _ (hfab y)]; exact hΦtb _)
  set K := ∫⁻ g, ENNReal.ofReal (‖g‖ ^ 2) ∂γₙ with hK_def
  have hK : K < ∞ := integral_lintegral_norm_sq_stdGaussian_lt_top
  refine ⟨M * (L : ℝ) ^ 2 * K.toReal, fun t ht => ?_⟩
  have := isProb_Qt (π := π) t
  have hpm : ∀ θ, pmean π t θ f ∈ Set.Icc a b := fun θ => by
    have := post_isProb (π := π) ht θ
    exact integral_mem_Icc' hfm hfab
  have hpmi := integrable_pmean_Qt (π := π) ht (hfi π)
  have i1 : Integrable (fun θ => pmean π t θ (fun y => Φ (f y))) (Qt π t) :=
    integrable_pmean_Qt ht (hΦfi π)
  have i2 : Integrable (fun θ => Φ (pmean π t θ f)) (Qt π t) := by
    refine (Integrable.of_bound (hΦtc.comp_aestronglyMeasurable hpmi.1) C0
      (Filter.Eventually.of_forall fun θ => hΦtb _)).congr
      (Filter.Eventually.of_forall fun θ => ?_)
    exact hΦt _ (hpm θ)
  rw [← integral_pmean_Qt ht _ (hΦfi π), ← integral_sub i2 i1]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  -- pointwise bound
  set G : Eₙ × Eₙ → ℝ≥0∞ := fun p => ENNReal.ofReal ((L : ℝ) ^ 2 * ‖p.2 - t⁻¹ • p.1‖ ^ 2)
    with hG_def
  have hGm : Measurable G := by fun_prop
  have hpt : ∀ θ, ENNReal.ofReal ‖Φ (pmean π t θ f) - pmean π t θ (fun y => Φ (f y))‖ ≤
      ENNReal.ofReal M * ∫⁻ y, G (θ, y) ∂(post π t θ) := by
    intro θ
    have := post_isProb (π := π) ht θ
    have hb := bregman_bound (μ := post π t θ) hM0 hM hfm hfab (hΦfi _) (f (t⁻¹ • θ))
    have hsqi : Integrable (fun y => (f y - f (t⁻¹ • θ)) ^ 2) (post π t θ) :=
      Integrable.of_bound (by fun_prop) ((max |a| |b| + |f (t⁻¹ • θ)|) ^ 2)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_pow]
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
          refine (abs_sub _ _).trans ?_
          have := hfb y; rw [Real.norm_eq_abs] at this; linarith)
    rw [Real.norm_eq_abs, abs_sub_comm]
    refine (ENNReal.ofReal_le_ofReal hb).trans ?_
    rw [ENNReal.ofReal_mul hM0, ofReal_integral_eq_lintegral_ofReal hsqi
      (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    gcongr with y
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hf.dist_le_mul y (t⁻¹ • θ)
    rw [Real.dist_eq, dist_eq_norm] at h1
    calc (f y - f (t⁻¹ • θ)) ^ 2 = |f y - f (t⁻¹ • θ)| ^ 2 := (sq_abs _).symm
      _ ≤ ((L : ℝ) * ‖y - t⁻¹ • θ‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = _ := by ring
  have htot : ∫⁻ θ, ENNReal.ofReal ‖Φ (pmean π t θ f) - pmean π t θ (fun y => Φ (f y))‖
      ∂(Qt π t) ≤ ENNReal.ofReal M * (ENNReal.ofReal ((L : ℝ) ^ 2 / t) * K) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul _ (measurable_lintegral_post_joint ht hGm),
      lintegral_post_Qt_joint ht hGm]
    gcongr
    have : ∀ x : Eₙ, ∫⁻ g, G (t • x + Real.sqrt t • g, x) ∂γₙ =
        ENNReal.ofReal ((L : ℝ) ^ 2 / t) * K := by
      intro x
      rw [hK_def, ← lintegral_const_mul _ (by fun_prop)]
      congr 1; funext g
      simp only [hG_def]
      rw [norm_sub_inv_smul_obs_sq ht, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    simp_rw [this]
    simp
  have hfin : ENNReal.ofReal M * (ENNReal.ofReal ((L : ℝ) ^ 2 / t) * K) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.ne)
  refine (ENNReal.toReal_mono hfin htot).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- **(L∞)** As `t → ∞`, `∫ Φ(pmean_t f) dQt → ∫ Φ(f) dπ`. -/
theorem tendsto_Ifun_top {J : Set ℝ} (hJ : IsOpen J) {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 2 Φ J)
    {a b : ℝ} (hab : Set.Icc a b ⊆ J) {f : Eₙ → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (hfab : ∀ y, f y ∈ Set.Icc a b) :
    Tendsto (fun t => ∫ θ, Φ (pmean π t θ f) ∂(Qt π t)) atTop (𝓝 (∫ y, Φ (f y) ∂π)) := by
  obtain ⟨C, hC⟩ := abs_Ifun_sub_le (π := π) hJ hΦ hab hf hfab
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun t => C / t) (Filter.Eventually.of_forall fun t => norm_nonneg _)
    ?_ (tendsto_const_nhds.div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact hC t ht


/-! ### (L0) The limit `t → 0⁺` -/

/-- the dominating function used at `t = 0` -/
def expDom (y : Eₙ) : ℝ :=
  1 + ∑ i, (Real.exp (⟪(n : ℝ) • EuclideanSpace.single i (1 : ℝ), y⟫) +
    Real.exp (⟪(-(n : ℝ)) • EuclideanSpace.single i (1 : ℝ), y⟫))

theorem norm_le_sum_abs (y : Eₙ) : ‖y‖ ≤ ∑ i, |y i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  simp only [Real.norm_eq_abs, sq_abs]
  calc ∑ i, y i ^ 2 = ∑ i, |y i| ^ 2 := by simp [sq_abs]
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

theorem exp_norm_le_expDom (y : Eₙ) : Real.exp ‖y‖ ≤ expDom y := by
  unfold expDom
  have hpos : ∀ i, 0 ≤ Real.exp (⟪(n : ℝ) • EuclideanSpace.single i (1 : ℝ), y⟫) +
      Real.exp (⟪(-(n : ℝ)) • EuclideanSpace.single i (1 : ℝ), y⟫) := fun i => by positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : y = 0 := Subsingleton.elim _ _
    subst this
    simp
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => |y i|)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have h1 : ‖y‖ ≤ n * |y i0| := by
      refine (norm_le_sum_abs y).trans ?_
      have := Finset.sum_le_card_nsmul Finset.univ (fun i => |y i|) (|y i0|)
        (fun i _ => hi0 i (Finset.mem_univ _))
      simpa using this
    have h2 : Real.exp ‖y‖ ≤ Real.exp (⟪(n : ℝ) • EuclideanSpace.single i0 (1 : ℝ), y⟫) +
        Real.exp (⟪(-(n : ℝ)) • EuclideanSpace.single i0 (1 : ℝ), y⟫) := by
      simp only [inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul,
        RCLike.conj_to_real]
      rcases le_total 0 (y i0) with h | h
      · rw [abs_of_nonneg h] at h1
        have := Real.exp_le_exp.2 h1
        have := Real.exp_pos (-(n : ℝ) * y i0)
        linarith
      · rw [abs_of_nonpos h] at h1
        have e : (n : ℝ) * -y i0 = -(n : ℝ) * y i0 := by ring
        rw [e] at h1
        have := Real.exp_le_exp.2 h1
        have := Real.exp_pos ((n : ℝ) * y i0)
        linarith
    have h3 := Finset.single_le_sum (fun i _ => hpos i) (Finset.mem_univ i0)
    linarith


theorem integrable_expDom (hexp : ∀ θ : Eₙ, Integrable (fun x => Real.exp ⟪θ, x⟫) π) :
    Integrable expDom π := by
  unfold expDom
  exact (integrable_const _).add (integrable_finsetSum _ fun i _ => (hexp _).add (hexp _))

theorem wt_le_expDom {s : ℝ} (hs : 0 ≤ s) {θ : Eₙ} (hθ : ‖θ‖ ≤ 1) (y : Eₙ) :
    wt s θ y ≤ expDom y := by
  refine le_trans ?_ (exp_norm_le_expDom y)
  unfold wt
  refine Real.exp_le_exp.2 ?_
  have h1 := real_inner_le_norm θ y
  have h2 : ‖θ‖ * ‖y‖ ≤ ‖y‖ := by
    have := norm_nonneg y; nlinarith
  have h3 : 0 ≤ s * ‖y‖ ^ 2 / 2 := by positivity
  linarith

theorem wt_zero_zero (y : Eₙ) : wt 0 0 y = 1 := by
  simp [wt]

theorem Zt_zero_zero : Zt π 0 0 = 1 := by
  simp [Zt, wt_zero_zero]

theorem post_zero_zero : post π 0 0 = π := by
  unfold post
  simp only [wt_zero_zero, Zt_zero_zero, div_one, ENNReal.ofReal_one]
  exact withDensity_one

/-- Continuity of `∫ g · wt` at `(t, θ) = (0, 0)`. -/
theorem tendsto_integral_mul_wt {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (hexp : ∀ θ : Eₙ, Integrable (fun x => Real.exp ⟪θ, x⟫) π)
    {T : α → ℝ} {Θ : α → Eₙ} (hT : Tendsto T l (𝓝 0)) (hT0 : ∀ᶠ a in l, 0 ≤ T a)
    (hΘ : Tendsto Θ l (𝓝 0)) {g : Eₙ → ℝ} (hg : AEStronglyMeasurable g π) {B : ℝ}
    (hgB : ∀ y, |g y| ≤ B) :
    Tendsto (fun a => ∫ y, g y * wt (T a) (Θ a) y ∂π) l (𝓝 (∫ y, g y ∂π)) := by
  have hlim : (fun y => g y) = fun y => g y * wt 0 0 y := by
    funext y; rw [wt_zero_zero, mul_one]
  rw [hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => B * expDom y)
    (Filter.Eventually.of_forall fun a => hg.mul (continuous_wt_right _ _).aestronglyMeasurable)
    ?_ ((integrable_expDom hexp).const_mul B) (Filter.Eventually.of_forall fun y => ?_)
  · have hΘ1 : ∀ᶠ a in l, ‖Θ a‖ ≤ 1 := by
      have := hΘ.norm
      rw [norm_zero] at this
      exact this.eventually (eventually_le_nhds one_pos)
    filter_upwards [hT0, hΘ1] with a ha1 ha2
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos _ _ _)]
    exact mul_le_mul (hgB y) (wt_le_expDom ha1 ha2 y) (wt_nonneg _ _ _)
      ((abs_nonneg _).trans (hgB y))
  · refine Tendsto.const_mul _ ?_
    have hc : Continuous (fun p : ℝ × Eₙ => wt p.1 p.2 y) := by unfold wt; fun_prop
    have := (hc.tendsto (0, 0)).comp (hT.prodMk_nhds hΘ)
    exact this

/-- **(L0)** Continuity of the posterior mean at `(t, θ) = (0, 0)`. -/
theorem tendsto_pmean_of_tendsto {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (hexp : ∀ θ : Eₙ, Integrable (fun x => Real.exp ⟪θ, x⟫) π)
    {T : α → ℝ} {Θ : α → Eₙ} (hT : Tendsto T l (𝓝 0)) (hT0 : ∀ᶠ a in l, 0 ≤ T a)
    (hΘ : Tendsto Θ l (𝓝 0)) {f : Eₙ → ℝ} (hf : AEStronglyMeasurable f π) {B : ℝ}
    (hfB : ∀ y, |f y| ≤ B) :
    Tendsto (fun a => pmean π (T a) (Θ a) f) l (𝓝 (∫ y, f y ∂π)) := by
  simp_rw [pmean_eq]
  have h1 := tendsto_integral_mul_wt hexp hT hT0 hΘ hf hfB
  have h2 := tendsto_integral_mul_wt (g := fun _ => (1 : ℝ)) hexp hT hT0 hΘ
    aestronglyMeasurable_const (B := 1) (fun _ => by simp)
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h2
  have := h1.div h2 one_ne_zero
  rw [div_one] at this
  exact this

theorem tendsto_pmean_zero (hexp : ∀ θ : Eₙ, Integrable (fun x => Real.exp ⟪θ, x⟫) π)
    {f : Eₙ → ℝ} (hf : AEStronglyMeasurable f π) {B : ℝ} (hfB : ∀ y, |f y| ≤ B) (x g : Eₙ) :
    Tendsto (fun t => pmean π t (t • x + Real.sqrt t • g) f) (𝓝[>] 0)
      (𝓝 (∫ y, f y ∂π)) := by
  have hT : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hS : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [Real.sqrt_zero] at this
  refine tendsto_pmean_of_tendsto hexp hT ?_ ?_ hf hfB
  · filter_upwards [self_mem_nhdsWithin] with t ht using le_of_lt ht
  · have := (hT.smul_const x).add (hS.smul_const g)
    simpa using this

theorem abs_pmean_le {t : ℝ} (ht : 0 < t) (θ : Eₙ) {f : Eₙ → ℝ} {B : ℝ} (hfB : ∀ y, |f y| ≤ B) :
    |pmean π t θ f| ≤ B := by
  have := post_isProb (π := π) ht θ
  have h := norm_integral_le_of_norm_le_const (μ := post π t θ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hfB y)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- **(L0)** As `t → 0⁺`, `∫ F(pmean_t f) dQt → F(∫ f dπ)`. -/
theorem tendsto_Ifun_zero (hexp : ∀ θ : Eₙ, Integrable (fun x => Real.exp ⟪θ, x⟫) π)
    {f : Eₙ → ℝ} (hf : Measurable f) {B : ℝ} (hfB : ∀ y, |f y| ≤ B)
    {F : ℝ → ℝ} (hF : Continuous F) :
    Tendsto (fun t => ∫ θ, F (pmean π t θ f) ∂(Qt π t)) (𝓝[>] 0) (𝓝 (F (∫ y, f y ∂π))) := by
  have hfi : Integrable f π := Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hfB y)
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := -B) (b := B)).exists_bound_of_continuousOn
    hF.continuousOn
  set φ : ℝ → Eₙ × Eₙ → Eₙ := fun t p => t • p.1 + Real.sqrt t • p.2 with hφ
  have hφm : ∀ t, Measurable (φ t) := fun t => by simp only [hφ]; fun_prop
  have hmeas : ∀ t, 0 < t → AEStronglyMeasurable (fun θ => F (pmean π t θ f)) (Qt π t) :=
    fun t ht => hF.comp_aestronglyMeasurable (integrable_pmean_Qt ht hfi).1
  have hrw : ∀ t, 0 < t → ∫ θ, F (pmean π t θ f) ∂(Qt π t) =
      ∫ p, F (pmean π t (φ t p) f) ∂(π.prod γₙ) := fun t ht => by
    rw [Qt, integral_map (hφm t).aemeasurable (by rw [← Qt]; exact hmeas t ht)]
  have hlim : Tendsto (fun t => ∫ p, F (pmean π t (φ t p) f) ∂(π.prod γₙ)) (𝓝[>] 0)
      (𝓝 (∫ _p, F (∫ y, f y ∂π) ∂(π.prod γₙ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C0) ?_ ?_
      (integrable_const _) (Filter.Eventually.of_forall fun p => ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (show AEStronglyMeasurable (fun θ => F (pmean π t θ f)) (Qt π t) from
        hmeas t ht).comp_measurable (hφm t)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine Filter.Eventually.of_forall fun p => hC0 _ ?_
      exact abs_le.1 (abs_pmean_le ht _ hfB)
    · exact (hF.tendsto _).comp (tendsto_pmean_zero hexp hf.aestronglyMeasurable hfB p.1 p.2)
  simp only [integral_const, probReal_univ, one_smul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hrw t ht).symm

/-- **(L0)**, version with `F` only continuous on `[a, b]` and `f` valued in `[a, b]`. -/
theorem tendsto_Ifun_zero_Icc (hexp : ∀ θ : Eₙ, Integrable (fun x => Real.exp ⟪θ, x⟫) π)
    {f : Eₙ → ℝ} (hf : Measurable f) {a b : ℝ} (hfab : ∀ y, f y ∈ Set.Icc a b)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc a b)) :
    Tendsto (fun t => ∫ θ, F (pmean π t θ f) ∂(Qt π t)) (𝓝[>] 0) (𝓝 (F (∫ y, f y ∂π))) := by
  have hle : a ≤ b := (hfab 0).1.trans (hfab 0).2
  set Ft : ℝ → ℝ := fun s => F (Set.projIcc a b hle s) with hFt_def
  have hFtc : Continuous Ft := hF.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun s => (Set.projIcc a b hle s).2)
  have hFt : ∀ s ∈ Set.Icc a b, Ft s = F s := fun s hs => by
    simp only [hFt_def, Set.projIcc_of_mem hle hs]
  have hfB : ∀ y, |f y| ≤ max |a| |b| := fun y => abs_le_max_abs_abs (hfab y).1 (hfab y).2
  have h := tendsto_Ifun_zero (π := π) hexp hf hfB hFtc
  rw [hFt _ (integral_mem_Icc' hf hfab)] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  have := post_isProb (π := π) ht θ
  exact hFt _ (integral_mem_Icc' hf hfab)

/-! ### Vector-valued joint tower and the covariance limit at `t = 0` -/

theorem euc_integral_apply {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : α → Eₙ}
    (hV : Integrable V μ) (i : Fin n) : (∫ a, V a ∂μ) i = ∫ a, V a i ∂μ :=
  ((EuclideanSpace.proj i : Eₙ →L[ℝ] ℝ).integral_comp_comm hV).symm

theorem measurable_pmean (ht : 0 < t) {f : Eₙ → ℝ} (hf : Measurable f) :
    Measurable (fun θ => pmean π t θ f) := by
  have hZ := measurable_Zt (π := π) ht
  simp_rw [pmean_eq]
  refine Measurable.div ?_ hZ
  exact (StronglyMeasurable.integral_prod_right' (ν := π)
    (f := fun p : Eₙ × Eₙ => f p.2 * wt t p.1 p.2)
    (by fun_prop : Measurable _).stronglyMeasurable).measurable

theorem stronglyMeasurable_integral_post_joint (ht : 0 < t) {G : Eₙ × Eₙ → Eₙ}
    (hG : Measurable G) : StronglyMeasurable (fun θ => ∫ x, G (θ, x) ∂(post π t θ)) := by
  have hZ := measurable_Zt (π := π) ht
  have e : (fun θ => ∫ x, G (θ, x) ∂(post π t θ)) =
      fun θ => ∫ x, (wt t θ x / Zt π t θ) • G (θ, x) ∂π := by
    funext θ
    rw [post, integral_withDensity_eq_integral_toReal_smul (measurable_post_density t θ)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1; funext x
    rw [ENNReal.toReal_ofReal (div_nonneg (wt_nonneg t θ x) (Zt_nonneg t θ))]
  rw [e]
  exact StronglyMeasurable.integral_prod_right' (ν := π)
    (f := fun p : Eₙ × Eₙ => (wt t p.1 p.2 / Zt π t p.1) • G p)
    (by fun_prop : Measurable _).stronglyMeasurable

/-- Joint tower property for vector-valued `G`. -/
theorem integral_post_Qt_joint_vec (ht : 0 < t) {G : Eₙ × Eₙ → Eₙ} (hG : Measurable G)
    (hint : Integrable (fun p : Eₙ × Eₙ => G (t • p.1 + Real.sqrt t • p.2, p.1)) (π.prod γₙ)) :
    ∫ θ, ∫ x, G (θ, x) ∂(post π t θ) ∂(Qt π t) =
      ∫ p, G (t • p.1 + Real.sqrt t • p.2, p.1) ∂(π.prod γₙ) := by
  have hsec : ∀ θ, Measurable (fun x => G (θ, x)) := fun θ =>
    hG.comp (measurable_const.prodMk measurable_id)
  obtain ⟨a1, b1, -⟩ := joint_aux_nonneg (π := π) ht (H := fun p => ‖G p‖) (by fun_prop)
    (fun p => norm_nonneg _) hint.norm
  have hVi : Integrable (fun θ => ∫ x, G (θ, x) ∂(post π t θ)) (Qt π t) :=
    b1.mono' (stronglyMeasurable_integral_post_joint ht hG).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => norm_integral_le_integral_norm _)
  refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
  change (∫ θ, ∫ x, G (θ, x) ∂(post π t θ) ∂(Qt π t)) i =
    (∫ p, G (t • p.1 + Real.sqrt t • p.2, p.1) ∂(π.prod γₙ)) i
  rw [euc_integral_apply hVi, euc_integral_apply hint]
  have hGi : Measurable (fun p => G p i) :=
    (EuclideanSpace.proj i : Eₙ →L[ℝ] ℝ).continuous.measurable.comp hG
  have e1 : (fun θ => (∫ x, G (θ, x) ∂(post π t θ)) i) =ᵐ[Qt π t]
      fun θ => ∫ x, G (θ, x) i ∂(post π t θ) := by
    filter_upwards [a1] with θ hθ
    exact euc_integral_apply ((integrable_norm_iff (hsec θ).aestronglyMeasurable).1 hθ) i
  rw [integral_congr_ae e1]
  exact integral_post_Qt_joint' ht (G := fun p => G p i) hGi
    ((EuclideanSpace.proj i : Eₙ →L[ℝ] ℝ).integrable_comp hint)

theorem integrable_norm_of_hexp (hexp : ∀ θ : Eₙ, Integrable (fun x => Real.exp ⟪θ, x⟫) π) :
    Integrable (fun y : Eₙ => ‖y‖) π :=
  (integrable_expDom hexp).mono' continuous_norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_norm]
      have := Real.add_one_le_exp ‖y‖
      linarith [exp_norm_le_expDom y])

/-- **(L0)** As `t → 0⁺`, `∫ pcov_t(f) dQt → Cov_π(f, X)`. -/
theorem tendsto_pcov_zero (hexp : ∀ θ : Eₙ, Integrable (fun x => Real.exp ⟪θ, x⟫) π)
    {f : Eₙ → ℝ} (hf : Measurable f) {B : ℝ} (hfB : ∀ y, |f y| ≤ B) :
    Tendsto (fun t => ∫ θ, pcov π t θ f ∂(Qt π t)) (𝓝[>] 0)
      (𝓝 (∫ y, (f y - ∫ z, f z ∂π) • y ∂π)) := by
  have h1 := integrable_norm_of_hexp hexp
  have hdom : Integrable (fun p : Eₙ × Eₙ => (2 * B) * ‖p.1‖) (π.prod γₙ) :=
    (h1.comp_fst γₙ).const_mul _
  set φ : ℝ → Eₙ × Eₙ → Eₙ := fun t p => t • p.1 + Real.sqrt t • p.2 with hφ
  have hφm : ∀ t, Measurable (φ t) := fun t => by simp only [hφ]; fun_prop
  have hbd : ∀ t, 0 < t → ∀ θ y, ‖(f y - pmean π t θ f) • y‖ ≤ 2 * B * ‖y‖ := by
    intro t ht θ y
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := abs_pmean_le (π := π) ht θ hfB
    have := hfB y
    have := abs_sub (f y) (pmean π t θ f)
    linarith
  have hrw : ∀ t, 0 < t → ∫ θ, pcov π t θ f ∂(Qt π t) =
      ∫ p, (f p.1 - pmean π t (φ t p) f) • p.1 ∂(π.prod γₙ) := by
    intro t ht
    have hGm : Measurable (fun q : Eₙ × Eₙ => (f q.2 - pmean π t q.1 f) • q.2) :=
      ((hf.comp measurable_snd).sub ((measurable_pmean ht hf).comp measurable_fst)).smul
        measurable_snd
    refine integral_post_Qt_joint_vec ht hGm (hdom.mono' ?_ ?_)
    · exact (hGm.comp (by fun_prop : Measurable fun p : Eₙ × Eₙ =>
        (t • p.1 + Real.sqrt t • p.2, p.1))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => hbd t ht _ _
  have hlim : Tendsto (fun t => ∫ p, (f p.1 - pmean π t (φ t p) f) • p.1 ∂(π.prod γₙ))
      (𝓝[>] 0) (𝓝 (∫ p, (f p.1 - ∫ z, f z ∂π) • p.1 ∂(π.prod γₙ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => (2 * B) * ‖p.1‖) ?_ ?_
      hdom (Filter.Eventually.of_forall fun p => ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (((hf.comp measurable_fst).sub ((measurable_pmean ht hf).comp (hφm t))).smul
        measurable_fst).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Filter.Eventually.of_forall fun p => hbd t ht _ _
    · exact (tendsto_const_nhds.sub
        (tendsto_pmean_zero hexp hf.aestronglyMeasurable hfB p.1 p.2)).smul_const p.1
  rw [integral_fun_fst (f := fun y => (f y - ∫ z, f z ∂π) • y), probReal_univ, one_smul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hrw t ht).symm

end PSBSL

end
end

-- ===== Extend.lean =====
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal ContDiff Convolution

noncomputable section

namespace PSBSL

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma ext_norm_gradient (f : E → ℝ) (x : E) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

lemma ext_tendsto_integral (μ : Measure E) [IsFiniteMeasure μ] (F : ℕ → E → ℝ) (G : E → ℝ)
    (B : ℝ) (hF : ∀ k, AEStronglyMeasurable (F k) μ) (hB : ∀ k x, ‖F k x‖ ≤ B)
    (hlim : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (G x))) :
    Tendsto (fun k => ∫ x, F k x ∂μ) atTop (𝓝 (∫ x, G x ∂μ)) :=
  tendsto_integral_of_dominated_convergence (fun _ => B) hF (integrable_const B)
    (fun k => ae_of_all _ (hB k)) (ae_of_all _ hlim)

/-- Passing the Φ-Sobolev inequality to a limit. -/
lemma ext_limit (μ : Measure E) [IsProbabilityMeasure μ]
    {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {C a b M : ℝ} (hab : Icc a b ⊆ J)
    (f : ℕ → E → ℝ) (h : E → ℝ) (hf : ∀ k, ContDiff ℝ 1 (f k))
    (hfab : ∀ k x, f k x ∈ Icc a b) (hM : ∀ k x, ‖fderiv ℝ (f k) x‖ ≤ M)
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (h x)))
    (hdlim : ∀ x, Tendsto (fun k => fderiv ℝ (f k) x) atTop (𝓝 (fderiv ℝ h x)))
    (hineq : ∀ k, PhiSobBayes.phiEnt μ Φ (f k) ≤
      C / 2 * ∫ x, deriv (deriv Φ) (f k x) * ‖gradient (f k) x‖ ^ 2 ∂μ) :
    PhiSobBayes.phiEnt μ Φ h ≤ C / 2 * ∫ x, deriv (deriv Φ) (h x) * ‖gradient h x‖ ^ 2 ∂μ := by
  have hhab : ∀ x, h x ∈ Icc a b := fun x =>
    isClosed_Icc.mem_of_tendsto (hlim x) (Eventually.of_forall fun k => hfab k x)
  have hΦc : ContinuousOn Φ (Icc a b) := hΦ.1.continuousOn.mono hab
  have hd1 : ContDiffOn ℝ ∞ (deriv Φ) J := hΦ.1.deriv_of_isOpen hJ.1 (by simp)
  have hd2 : ContDiffOn ℝ ∞ (deriv (deriv Φ)) J := hd1.deriv_of_isOpen hJ.1 (by simp)
  have hΦ2c : ContinuousOn (deriv (deriv Φ)) (Icc a b) := hd2.continuousOn.mono hab
  -- general composition limit
  have hcomp : ∀ g : ℝ → ℝ, ContinuousOn g (Icc a b) → ∀ (u : ℕ → ℝ) (v : ℝ),
      (∀ k, u k ∈ Icc a b) → v ∈ Icc a b → Tendsto u atTop (𝓝 v) →
      Tendsto (fun k => g (u k)) atTop (𝓝 (g v)) := by
    intro g hg u v hu hv huv
    exact (hg v hv).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨huv, Eventually.of_forall hu⟩)
  obtain ⟨B1, hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦc
  obtain ⟨B2, hB2⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦ2c
  obtain ⟨B0, hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_id (s := Icc a b))
  have hfc : ∀ k, Continuous (f k) := fun k => (hf k).continuous
  -- ∫ f k → ∫ h
  have hI : Tendsto (fun k => ∫ x, f k x ∂μ) atTop (𝓝 (∫ x, h x ∂μ)) :=
    ext_tendsto_integral μ f h B0 (fun k => (hfc k).aestronglyMeasurable)
      (fun k x => hB0 _ (hfab k x)) hlim
  have hIab : ∀ k, ∫ x, f k x ∂μ ∈ Icc a b := fun k =>
    (convex_Icc a b).integral_mem isClosed_Icc (ae_of_all _ (hfab k))
      (Integrable.of_bound (hfc k).aestronglyMeasurable B0
        (Eventually.of_forall fun x => hB0 _ (hfab k x)))
  have hIhab : ∫ x, h x ∂μ ∈ Icc a b :=
    isClosed_Icc.mem_of_tendsto hI (Eventually.of_forall hIab)
  -- ∫ Φ (f k) → ∫ Φ h
  have hIΦ : Tendsto (fun k => ∫ x, Φ (f k x) ∂μ) atTop (𝓝 (∫ x, Φ (h x) ∂μ)) :=
    ext_tendsto_integral μ (fun k x => Φ (f k x)) (fun x => Φ (h x)) B1
      (fun k => (hΦc.comp_continuous (hfc k) (hfab k)).aestronglyMeasurable)
      (fun k x => hB1 _ (hfab k x))
      (fun x => hcomp Φ hΦc _ _ (fun k => hfab k x) (hhab x) (hlim x))
  have hEnt : Tendsto (fun k => PhiSobBayes.phiEnt μ Φ (f k)) atTop
      (𝓝 (PhiSobBayes.phiEnt μ Φ h)) :=
    hIΦ.sub (hcomp Φ hΦc _ _ hIab hIhab hI)
  -- energy
  simp only [ext_norm_gradient] at hineq ⊢
  have hEn : Tendsto (fun k => ∫ x, deriv (deriv Φ) (f k x) * ‖fderiv ℝ (f k) x‖ ^ 2 ∂μ)
      atTop (𝓝 (∫ x, deriv (deriv Φ) (h x) * ‖fderiv ℝ h x‖ ^ 2 ∂μ)) := by
    refine ext_tendsto_integral μ _ _ (B2 * M ^ 2) (fun k => ?_) (fun k x => ?_) (fun x => ?_)
    · exact ((hΦ2c.comp_continuous (hfc k) (hfab k)).mul
        (((hf k).continuous_fderiv one_ne_zero).norm.pow 2)).aestronglyMeasurable
    · rw [norm_mul, norm_pow, norm_norm]
      have h0 : 0 ≤ ‖fderiv ℝ (f k) x‖ := norm_nonneg _
      have h1 := hB2 _ (hfab k x)
      have h2 := hM k x
      exact mul_le_mul h1 (pow_le_pow_left₀ h0 h2 2) (by positivity) ((norm_nonneg _).trans h1)
    · exact (hcomp _ hΦ2c _ _ (fun k => hfab k x) (hhab x) (hlim x)).mul
        ((hdlim x).norm.pow 2)
  exact le_of_tendsto_of_tendsto' hEnt (hEn.const_mul _) hineq


/-- The fixed cutoff bump: `1` on the unit ball, supported in the ball of radius `2`. -/
def ext_bump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

lemma ext_bump_fderiv_bound : ∃ L, ∀ x : E, ‖fderiv ℝ (ext_bump (n := n)) x‖ ≤ L :=
  ((ext_bump (n := n)).contDiff (n := 1).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    ((ext_bump (n := n)).hasCompactSupport.fderiv ℝ)

lemma ext_cut_hasFDerivAt (g : E → ℝ) (hg : Differentiable ℝ g) (a s : ℝ) (x : E) :
    HasFDerivAt (fun y => a + ext_bump (n := n) (s • y) * (g y - a))
      (ext_bump (n := n) (s • x) • fderiv ℝ g x +
        (g x - a) • (s • fderiv ℝ (ext_bump (n := n)) (s • x))) x := by
  have h1 : HasFDerivAt (fun y : E => s • y) (s • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul s
  have h2 : HasFDerivAt (fun y : E => ext_bump (n := n) (s • y))
      ((fderiv ℝ (ext_bump (n := n)) (s • x)).comp (s • ContinuousLinearMap.id ℝ E)) x :=
    ((ext_bump (n := n)).contDiff (n := 1).differentiable one_ne_zero
      (s • x)).hasFDerivAt.comp x h1
  have h3 : HasFDerivAt (fun y => g y - a) (fderiv ℝ g x) x :=
    (hg x).hasFDerivAt.sub_const a
  have heq : (fderiv ℝ (ext_bump (n := n)) (s • x)).comp (s • ContinuousLinearMap.id ℝ E) =
      s • fderiv ℝ (ext_bump (n := n)) (s • x) := by
    ext v; simp
  rw [heq] at h2
  exact (h2.mul h3).const_add a


lemma ext_bump_eventually_one (x : E) :
    ∀ᶠ k : ℕ in atTop, ext_bump (n := n) ((1 / ((k : ℝ) + 1)) • x) = 1 := by
  filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with k hk
  apply ContDiffBump.one_of_mem_closedBall
  have hk' : ‖x‖ ≤ (k : ℝ) + 1 := by
    have := Nat.le_ceil ‖x‖
    have : (⌈‖x‖⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.2 hpos)]
  show 1 / ((k : ℝ) + 1) * ‖x‖ ≤ 1
  rw [div_mul_eq_mul_div, one_mul, div_le_one hpos]
  exact hk'

/-- The Φ-Sobolev inequality for smooth functions with values in `[a,b]` and bounded gradient. -/
lemma ext_smooth (μ : Measure E) [IsProbabilityMeasure μ]
    {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {C : ℝ} (hS : PhiSobBayes.PhiSobolev μ J Φ C)
    {a b M : ℝ} (hab : Icc a b ⊆ J)
    (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (hgab : ∀ x, g x ∈ Icc a b)
    (hM : ∀ x, ‖fderiv ℝ g x‖ ≤ M) :
    PhiSobBayes.phiEnt μ Φ g ≤ C / 2 * ∫ x, deriv (deriv Φ) (g x) * ‖gradient g x‖ ^ 2 ∂μ := by
  obtain ⟨L, hL⟩ := ext_bump_fderiv_bound (n := n)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hab' : a ≤ b := (hgab 0).1.trans (hgab 0).2
  obtain ⟨s, hs_def⟩ : ∃ s : ℕ → ℝ, s = fun k : ℕ => 1 / ((k : ℝ) + 1) := ⟨_, rfl⟩
  have hs0 : ∀ k, 0 < s k := fun k => by subst hs_def; positivity
  have hs1 : ∀ k, s k ≤ 1 := fun k => by
    subst hs_def; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  obtain ⟨f, hf_def⟩ : ∃ f : ℕ → E → ℝ,
    f = fun k y => a + ext_bump (n := n) (s k • y) * (g y - a) := ⟨_, rfl⟩
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hfd : ∀ k x, fderiv ℝ (f k) x = ext_bump (n := n) (s k • x) • fderiv ℝ g x +
      (g x - a) • (s k • fderiv ℝ (ext_bump (n := n)) (s k • x)) := fun k x =>
    by subst hf_def; exact (ext_cut_hasFDerivAt g hgd a (s k) x).fderiv
  have hsmooth : ∀ k, ContDiff ℝ ∞ (fun y => ext_bump (n := n) (s k • y) * (g y - a)) :=
    fun k => by
      have hb : ContDiff ℝ ∞ (fun y : E => ext_bump (n := n) y) := (ext_bump (n := n)).contDiff
      have hsc : ContDiff ℝ ∞ (fun y : E => s k • y) := contDiff_id.const_smul (s k)
      have h1 : ContDiff ℝ ∞ (fun y : E => ext_bump (n := n) (s k • y)) := hb.comp hsc
      have h2 : ContDiff ℝ ∞ (fun y : E => g y - a) := hg.sub contDiff_const
      exact h1.mul h2
  have hfab : ∀ k x, f k x ∈ Icc a b := by
    intro k x
    have h0 := (ext_bump (n := n)).nonneg (x := s k • x)
    have h1 := (ext_bump (n := n)).le_one (x := s k • x)
    have h2 := hgab x
    subst hf_def
    simp only [mem_Icc] at h2 ⊢
    constructor <;> nlinarith
  have hfT : ∀ k, f k ∈ PhiSobBayes.testClass n J := by
    intro k
    refine ⟨⟨a, fun y => ext_bump (n := n) (s k • y) * (g y - a), hsmooth k, ?_, by rw [hf_def]⟩,
      fun x => hab (hfab k x)⟩
    have : HasCompactSupport (fun y : E => ext_bump (n := n) (s k • y)) :=
      (ext_bump (n := n)).hasCompactSupport.comp_smul (hs0 k).ne'
    exact this.mul_right
  have hgab' : ∀ x, |g x - a| ≤ b - a := fun x => by
    rw [abs_of_nonneg (by linarith [(hgab x).1])]; linarith [(hgab x).2]
  have hterm2 : ∀ k x, ‖(g x - a) • (s k • fderiv ℝ (ext_bump (n := n)) (s k • x))‖ ≤
      (b - a) * L * s k := by
    intro k x
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hs0 k)]
    have := hL (s k • x)
    have := hgab' x
    have := hs0 k
    calc |g x - a| * (s k * ‖fderiv ℝ (ext_bump (n := n)) (s k • x)‖)
        ≤ (b - a) * (s k * L) := by gcongr
      _ = (b - a) * L * s k := by ring
  refine ext_limit μ hJ hΦ (M := M + (b - a) * L) hab f g
    (fun k => by rw [hf_def]; exact (contDiff_const.add (hsmooth k)).of_le (by simp)) hfab ?_ ?_ ?_
    (fun k => hS _ (hfT k))
  · intro k x
    rw [hfd]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖ext_bump (n := n) (s k • x) • fderiv ℝ g x‖ ≤ M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ext_bump (n := n)).nonneg]
      calc ext_bump (n := n) (s k • x) * ‖fderiv ℝ g x‖ ≤ 1 * M :=
            mul_le_mul (ext_bump (n := n)).le_one (hM x) (norm_nonneg _) zero_le_one
        _ = M := one_mul M
    have h2 := hterm2 k x
    have : (b - a) * L * s k ≤ (b - a) * L :=
      mul_le_of_le_one_right (mul_nonneg (by linarith) hL0) (hs1 k)
    linarith
  · intro x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ext_bump_eventually_one x] with k hk
    rw [hs_def] at hf_def
    simp only [hf_def, hk]; ring
  · intro x
    simp_rw [hfd]
    have hA : Tendsto (fun k => ext_bump (n := n) (s k • x) • fderiv ℝ g x) atTop
        (𝓝 (fderiv ℝ g x)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ext_bump_eventually_one x] with k hk
      simp only [hs_def, hk, one_smul]
    have hs : Tendsto s atTop (𝓝 0) := by rw [hs_def]; exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hB : Tendsto (fun k => (g x - a) • (s k • fderiv ℝ (ext_bump (n := n)) (s k • x)))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => hterm2 k x) ?_
      simpa using hs.const_mul ((b - a) * L)
    simpa using hA.add hB


/-- The mollifiers: normalized bumps supported in the ball of radius `1/(k+1)`. -/
def ext_moll (k : ℕ) : ContDiffBump (0 : E) :=
  ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩

lemma ext_moll_rOut_tendsto : Tendsto (fun k => (ext_moll (n := n) k).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma ext_moll_hasFDerivAt (k : ℕ) (h : E → ℝ) (hh : ContDiff ℝ 1 h) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ h x‖ ≤ M) (x₀ : E) :
    HasFDerivAt ((ext_moll (n := n) k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h)
      (((ext_moll (n := n) k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fderiv ℝ h) x₀) x₀ := by
  set ρ := (ext_moll (n := n) k).normed volume with hρ
  have hρc : Continuous ρ := (ext_moll (n := n) k).continuous_normed
  have hρcs : HasCompactSupport ρ := (ext_moll (n := n) k).hasCompactSupport_normed
  have hρi : Integrable ρ volume := (ext_moll (n := n) k).integrable_normed
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => (ext_moll (n := n) k).nonneg_normed t
  have hdc : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have e1 : (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) =
      fun x => ∫ t, ρ t • h (x - t) := by
    ext x; simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  have e2 : (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ h) x₀ =
      ∫ t, ρ t • fderiv ℝ h (x₀ - t) := by
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [e1, e2]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun x t => ρ t • h (x - t)) (F' := fun x t => ρ t • fderiv ℝ h (x - t))
    (bound := fun t => ρ t * M)
    Filter.univ_mem ?_ ?_ ?_ ?_ (hρi.mul_const M) ?_
  · exact Eventually.of_forall fun x =>
      (hρc.smul (hh.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact (hρc.smul (hh.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (hρcs.smul_right)
  · exact (hρc.smul (hdc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine ae_of_all _ fun t x _ => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact mul_le_mul_of_nonneg_left (hM _) (hρ0 t)
  · refine ae_of_all _ fun t x _ => ?_
    have h1 : HasFDerivAt (fun x => h (x - t)) (fderiv ℝ h (x - t)) x :=
      (hasFDerivAt_comp_sub t).2 (hd (x - t)).hasFDerivAt
    exact h1.const_smul (ρ t)


/-- **Extension of the Φ-Sobolev inequality** from the test class to `C¹` functions with values in
a compact subinterval `[a,b] ⊆ J` and bounded gradient. -/
theorem phiSobolev_extend {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ} (hΦ : PhiSobBayes.AdmissiblePhi J Φ)
    {C : ℝ} (hS : PhiSobBayes.PhiSobolev μ J Φ C) {a b : ℝ} (hab : Set.Icc a b ⊆ J)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ 1 h) (hhab : ∀ x, h x ∈ Set.Icc a b)
    (hgrad : ∃ M, ∀ x, ‖gradient h x‖ ≤ M) :
    PhiSobBayes.phiEnt μ Φ h ≤ C / 2 * ∫ x, deriv (deriv Φ) (h x) * ‖gradient h x‖ ^ 2 ∂μ := by
  obtain ⟨M, hM⟩ := hgrad
  simp only [ext_norm_gradient] at hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hab' : a ≤ b := (hhab 0).1.trans (hhab 0).2
  have hdc : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  let ρ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k => (ext_moll (n := n) k).normed volume
  let f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
    ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h
  have hfs : ∀ k, ContDiff ℝ ∞ (f k) := fun k =>
    (ext_moll (n := n) k).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (ext_moll (n := n) k).contDiff_normed
      hh.continuous.locallyIntegrable
  have hfd : ∀ k x, fderiv ℝ (f k) x =
      (ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ h) x := fun k x =>
    (ext_moll_hasFDerivAt k h hh hM x).fderiv
  have hfab : ∀ k x, f k x ∈ Icc a b := by
    intro k x
    have := dist_convolution_le (μ := volume) (z₀ := (a + b) / 2) (x₀ := x)
      (R := (ext_moll (n := n) k).rOut) (ε := (b - a) / 2) (by linarith)
      (ext_moll (n := n) k).support_normed_eq.subset (ext_moll (n := n) k).nonneg_normed
      (ext_moll (n := n) k).integral_normed hh.continuous.aestronglyMeasurable
      (fun y _ => by
        rw [Real.dist_eq, abs_le]; constructor <;> linarith [(hhab y).1, (hhab y).2])
    rw [Real.dist_eq, abs_le] at this
    constructor <;> linarith [this.1, this.2]
  have hfM : ∀ k x, ‖fderiv ℝ (f k) x‖ ≤ M := by
    intro k x
    rw [hfd]
    have := dist_convolution_le (μ := volume) (z₀ := (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      (x₀ := x) (R := (ext_moll (n := n) k).rOut) (ε := M) hM0
      (ext_moll (n := n) k).support_normed_eq.subset (ext_moll (n := n) k).nonneg_normed
      (ext_moll (n := n) k).integral_normed hdc.aestronglyMeasurable
      (fun y _ => by rw [dist_zero_right]; exact hM y)
    rwa [dist_zero_right] at this
  refine ext_limit μ hJ hΦ hab f h (fun k => (hfs k).of_le (by simp)) hfab hfM ?_ ?_
    (fun k => ext_smooth μ hJ hΦ hS hab (f k) (hfs k) (hfab k) (hfM k))
  · intro x
    exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      ext_moll_rOut_tendsto hh.continuous x
  · intro x
    simp_rw [hfd]
    exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      ext_moll_rOut_tendsto hdc x

end PSBSL

end
end

-- ===== Jensen.lean =====
section

/-! Jensen-type inequality for admissible `Φ`:
`Φ''(E h) (E |g|)² ≤ E[Φ''(h) g²]` (uses concavity of `1/Φ''`). -/

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace PSBSL

/-- elementary: if `2 S ≤ λ A + B / λ` for all `λ > 0`, `S ≥ 0`, `A ≥ 0` then `S² ≤ A B`. -/
lemma sq_le_of_forall_amgm {S A B : ℝ} (hS : 0 ≤ S) (hA : 0 ≤ A) (hB0 : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → 2 * S ≤ l * A + B / l) : S ^ 2 ≤ A * B := by
  rcases hS.eq_or_lt with hS0 | hSpos
  · rw [← hS0]; simpa using mul_nonneg hA hB0
  rcases hA.eq_or_lt with hA0 | hApos
  · -- A = 0: 2S ≤ B/l for all l, contradiction for large l
    exfalso
    have hB : 0 < B := by
      have := h 1 one_pos; rw [← hA0] at this; simp at this; linarith
    have := h (B / S) (div_pos hB hSpos)
    rw [← hA0, mul_zero, zero_add] at this
    have e : B / (B / S) = S := by field_simp
    rw [e] at this
    linarith
  · have := h (S / A) (div_pos hSpos hApos)
    rw [div_mul_cancel₀ _ hApos.ne', div_div_eq_mul_div] at this
    have h2 : S ≤ B * A / S := by linarith
    rw [le_div_iff₀ hSpos] at h2
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

lemma phi_jensen (P : Measure Ω) [IsProbabilityMeasure P] {J : Set ℝ}
    (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ} (hΦ : PhiSobBayes.AdmissiblePhi J Φ)
    {a b : ℝ} (hab : Set.Icc a b ⊆ J) (h : Ω → ℝ) (hh : Measurable h)
    (hhab : ∀ o, h o ∈ Set.Icc a b) (g : Ω → ℝ) (hg : Measurable g)
    (hgb : ∃ C, ∀ o, |g o| ≤ C) :
    deriv (deriv Φ) (∫ o, h o ∂P) * (∫ o, |g o| ∂P) ^ 2 ≤
      ∫ o, deriv (deriv Φ) (h o) * g o ^ 2 ∂P := by
  set ψ := deriv (deriv Φ) with hψ
  have hd1 : ContDiffOn ℝ ∞ (deriv Φ) J := hΦ.1.deriv_of_isOpen hJ.1 (by simp)
  have hd2 : ContDiffOn ℝ ∞ (deriv (deriv Φ)) J := hd1.deriv_of_isOpen hJ.1 (by simp)
  have hψc : ContinuousOn ψ J := hd2.continuousOn
  have hψpos : ∀ z ∈ J, 0 < ψ z := hΦ.2.1
  have hcc : ContinuousOn ψ (Set.Icc a b) := hψc.mono hab
  -- bounds of ψ on [a,b]
  have hΩ : (Set.univ : Set Ω).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have := measure_univ (μ := P)
    rw [hc] at this; simp at this
  obtain ⟨o0, -⟩ := hΩ
  have hne : (Set.Icc a b).Nonempty := ⟨h o0, hhab o0⟩
  have hab' : a ≤ b := (hhab o0).1.trans (hhab o0).2
  obtain ⟨zmin, hzmin, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcc
  obtain ⟨zmax, hzmax, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcc
  have hlo : ∀ o, ψ zmin ≤ ψ (h o) := fun o => hmin (hhab o)
  have hhi : ∀ o, ψ (h o) ≤ ψ zmax := fun o => hmax (hhab o)
  have hpmin : 0 < ψ zmin := hψpos _ (hab hzmin)
  obtain ⟨C, hC⟩ := hgb
  have hψh_meas : Measurable (fun o => ψ (h o)) := by
    have hc : Continuous (fun z => ψ (Set.projIcc a b hab' z)) :=
      hcc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        (fun z => (Set.projIcc a b hab' z).2)
    have : (fun o => ψ (h o)) = (fun z => ψ (Set.projIcc a b hab' z)) ∘ h := by
      funext o; simp [Set.projIcc_of_mem hab' (hhab o)]
    rw [this]; exact hc.measurable.comp hh
  -- integrability
  have hint_h : Integrable h P :=
    Integrable.of_bound hh.aestronglyMeasurable (max |a| |b|) (Filter.Eventually.of_forall
      fun o => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> [skip; skip] <;>
          [nlinarith [le_max_left |a| |b|, neg_abs_le a, (hhab o).1];
           nlinarith [le_max_right |a| |b|, le_abs_self b, (hhab o).2]])
  have hint_A : Integrable (fun o => ψ (h o) * g o ^ 2) P :=
    Integrable.of_bound (hψh_meas.mul (hg.pow_const 2)).aestronglyMeasurable (ψ zmax * C ^ 2)
      (Filter.Eventually.of_forall fun o => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hlo o |>.trans' hpmin.le) (sq_nonneg _))]
        have h1 : g o ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC o) 2
        exact mul_le_mul (hhi o) h1 (sq_nonneg _) (hpmin.le.trans (hlo o |>.trans (hhi o))))
  have hint_B : Integrable (fun o => (ψ (h o))⁻¹) P :=
    Integrable.of_bound hψh_meas.inv.aestronglyMeasurable (ψ zmin)⁻¹
      (Filter.Eventually.of_forall fun o => by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpmin.trans_le (hlo o)))]
        exact inv_anti₀ hpmin (hlo o))
  have hint_g : Integrable (fun o => |g o|) P :=
    Integrable.of_bound hg.abs.aestronglyMeasurable C (Filter.Eventually.of_forall fun o => by
      rw [Real.norm_eq_abs, abs_abs]; exact hC o)
  -- Jensen for the concave 1/ψ on [a,b]
  have hmem : (∫ o, h o ∂P) ∈ Set.Icc a b := by
    constructor
    · calc a = ∫ _o, a ∂P := by simp
        _ ≤ ∫ o, h o ∂P := integral_mono (integrable_const _) hint_h (fun o => (hhab o).1)
    · calc ∫ o, h o ∂P ≤ ∫ _o, b ∂P := integral_mono hint_h (integrable_const _) (fun o => (hhab o).2)
        _ = b := by simp
  have hjen : ∫ o, (ψ (h o))⁻¹ ∂P ≤ (ψ (∫ o, h o ∂P))⁻¹ := by
    have hconc : ConcaveOn ℝ (Set.Icc a b) (fun z => (ψ z)⁻¹) := hΦ.2.2.subset hab (convex_Icc a b)
    have hcont : ContinuousOn (fun z => (ψ z)⁻¹) (Set.Icc a b) :=
      hcc.inv₀ (fun z hz => (hψpos z (hab hz)).ne')
    exact hconc.le_map_integral hcont isClosed_Icc (Filter.Eventually.of_forall hhab) hint_h hint_B
  -- AM-GM pointwise
  set A := ∫ o, ψ (h o) * g o ^ 2 ∂P
  set B := ∫ o, (ψ (h o))⁻¹ ∂P
  set S := ∫ o, |g o| ∂P
  have hA : 0 ≤ A := integral_nonneg fun o =>
    mul_nonneg (hpmin.le.trans (hlo o)) (sq_nonneg _)
  have hS : 0 ≤ S := integral_nonneg fun o => abs_nonneg _
  have hamgm : ∀ l : ℝ, 0 < l → 2 * S ≤ l * A + B / l := by
    intro l hl
    have hpt : ∀ o, 2 * |g o| ≤ l * (ψ (h o) * g o ^ 2) + (ψ (h o))⁻¹ / l := by
      intro o
      have hp : 0 < ψ (h o) := hpmin.trans_le (hlo o)
      set q := l * ψ (h o) with hq
      have hqpos : 0 < q := mul_pos hl hp
      have key : 2 * |g o| * q ≤ q ^ 2 * |g o| ^ 2 + 1 := by nlinarith [sq_nonneg (q * |g o| - 1)]
      calc 2 * |g o| = (2 * |g o| * q) / q := by field_simp
        _ ≤ (q ^ 2 * |g o| ^ 2 + 1) / q := div_le_div_of_nonneg_right key hqpos.le
        _ = l * (ψ (h o) * g o ^ 2) + (ψ (h o))⁻¹ / l := by
          rw [sq_abs, hq]; field_simp
    calc 2 * S = ∫ o, 2 * |g o| ∂P := by rw [integral_const_mul]
      _ ≤ ∫ o, (l * (ψ (h o) * g o ^ 2) + (ψ (h o))⁻¹ / l) ∂P :=
          integral_mono (hint_g.const_mul 2) ((hint_A.const_mul l).add (hint_B.div_const l)) hpt
      _ = l * A + B / l := by rw [integral_add (hint_A.const_mul l) (hint_B.div_const l),
            integral_const_mul, integral_div]
  have hB0 : 0 ≤ B := integral_nonneg fun o => (inv_pos.2 (hpmin.trans_le (hlo o))).le
  have hsq := sq_le_of_forall_amgm hS hA hB0 hamgm
  have hψm : 0 < ψ (∫ o, h o ∂P) := hψpos _ (hab hmem)
  calc ψ (∫ o, h o ∂P) * S ^ 2 ≤ ψ (∫ o, h o ∂P) * (A * B) :=
        mul_le_mul_of_nonneg_left hsq hψm.le
    _ ≤ ψ (∫ o, h o ∂P) * (A * (ψ (∫ o, h o ∂P))⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hjen hA) hψm.le
    _ = A := by field_simp

end PSBSL

end
end

-- ===== OutSob.lean =====
section

/-! Φ-Sobolev inequality for the output law `Qt μ t` by tensorization (Lemma A.19). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

namespace PSBSL

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "γₙ" => stdGaussian (EuclideanSpace ℝ (Fin n))

/-- the affine map `(x, g) ↦ t x + √t g` -/
def outMap (t : ℝ) (p : E × E) : E := t • p.1 + Real.sqrt t • p.2

lemma measurable_outMap (t : ℝ) : Measurable (outMap (n := n) t) := by
  unfold outMap; fun_prop

/-- the Gaussian channel kernel `x ↦ law of t x + √t G` -/
def outKernel (t : ℝ) : Kernel E E :=
  ((Kernel.deterministic id measurable_id) ×ₖ (Kernel.const E γₙ)).map (outMap t)

instance (t : ℝ) : IsMarkovKernel (outKernel (n := n) t) := by
  unfold outKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_outMap t)

lemma outKernel_apply (t : ℝ) (x : E) :
    outKernel t x = Measure.map (fun g => t • x + Real.sqrt t • g) γₙ := by
  unfold outKernel
  rw [Kernel.map_apply _ (measurable_outMap t), Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map (measurable_outMap t) (by fun_prop)]
  rfl

lemma bind_outKernel (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) :
    μ.bind (outKernel t) = Qt μ t := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Qt,
    Measure.map_apply (by fun_prop) hs, Measure.prod_apply (by exact (measurable_outMap t) hs)]
  congr 1; funext x
  rw [outKernel_apply, Measure.map_apply (by fun_prop) hs]
  rfl

lemma integral_outKernel (t : ℝ) (x : E) (f : E → ℝ) (hf : Continuous f) :
    ∫ θ, f θ ∂(outKernel t x) = ∫ g, f (t • x + Real.sqrt t • g) ∂γₙ := by
  rw [outKernel_apply, integral_map (by fun_prop) hf.aestronglyMeasurable]


/-! ### Analytic helpers -/

lemma gradient_comp_affine (h : E → ℝ) (hh : Differentiable ℝ h) (c : ℝ) (y g : E) :
    gradient (fun g => h (y + c • g)) g = c • gradient h (y + c • g) := by
  have hd : HasFDerivAt (fun g => h (y + c • g)) (c • fderiv ℝ h (y + c • g)) g := by
    have := (hh (y + c • g)).hasFDerivAt.comp g (((hasFDerivAt_id g).const_smul c).const_add y)
    refine this.congr_fderiv ?_
    ext v; simp
  unfold gradient; rw [hd.fderiv, map_smul]

lemma continuous_gradient_of_contDiff (h : E → ℝ) (hh : ContDiff ℝ 1 h) :
    Continuous (gradient h) := by
  have : gradient h = (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ h := by
    funext x; rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hh.continuous_fderiv one_ne_zero)

lemma integrable_of_cont_bdd {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ) (hf : Continuous f) (K : ℝ) (hK : ∀ x, ‖f x‖ ≤ K) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable K (Eventually.of_forall hK)

lemma integral_mem_Icc {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : AEStronglyMeasurable f ν) {a b : ℝ} (hfab : ∀ x, f x ∈ Icc a b) :
    ∫ x, f x ∂ν ∈ Icc a b := by
  have hint : Integrable f ν := Integrable.of_bound hf (max |a| |b|) (Eventually.of_forall
    fun o => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · nlinarith [le_max_left |a| |b|, neg_abs_le a, (hfab o).1]
      · nlinarith [le_max_right |a| |b|, le_abs_self b, (hfab o).2])
  constructor
  · calc a = ∫ _o, a ∂ν := by simp
      _ ≤ ∫ o, f o ∂ν := integral_mono (integrable_const _) hint (fun o => (hfab o).1)
  · calc ∫ o, f o ∂ν ≤ ∫ _o, b ∂ν := integral_mono hint (integrable_const _) (fun o => (hfab o).2)
      _ = b := by simp

/-- integrating over `Qt` as an iterated integral -/
lemma integral_Qt_iter (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ) (F : E → ℝ)
    (hF : Continuous F) (K : ℝ) (hK : ∀ x, ‖F x‖ ≤ K) :
    ∫ θ, F θ ∂(Qt μ t) = ∫ x, ∫ g, F (t • x + Real.sqrt t • g) ∂γₙ ∂μ := by
  rw [Qt, integral_map (by fun_prop) hF.aestronglyMeasurable]
  rw [integral_prod]
  exact integrable_of_cont_bdd _ _ (by fun_prop) K (fun p => hK _)


lemma admissible_contOn {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) :
    ContinuousOn Φ J ∧ ContinuousOn (deriv (deriv Φ)) J := by
  have hd1 : ContDiffOn ℝ ∞ (deriv Φ) J := hΦ.1.deriv_of_isOpen hJ.1 (by simp)
  have hd2 : ContDiffOn ℝ ∞ (deriv (deriv Φ)) J := hd1.deriv_of_isOpen hJ.1 (by simp)
  exact ⟨hΦ.1.continuousOn, hd2.continuousOn⟩

/-- the integrand `Φ''(h) ‖∇h‖²` is continuous, bounded and nonnegative -/
lemma integrand_facts {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {a b : ℝ} (hab : Icc a b ⊆ J)
    (h : E → ℝ) (hh : ContDiff ℝ 1 h) (hhab : ∀ x, h x ∈ Icc a b) {M : ℝ}
    (hM : ∀ x, ‖gradient h x‖ ≤ M) :
    Continuous (fun θ => deriv (deriv Φ) (h θ) * ‖gradient h θ‖ ^ 2) ∧
    (∃ K, ∀ θ, ‖deriv (deriv Φ) (h θ) * ‖gradient h θ‖ ^ 2‖ ≤ K) ∧
    (∀ θ, 0 ≤ deriv (deriv Φ) (h θ) * ‖gradient h θ‖ ^ 2) := by
  obtain ⟨-, hψc⟩ := admissible_contOn hJ hΦ
  have hψh : Continuous (fun θ => deriv (deriv Φ) (h θ)) :=
    (hψc.mono hab).comp_continuous hh.continuous hhab
  have hgc := continuous_gradient_of_contDiff h hh
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hψc.mono hab)
  refine ⟨hψh.mul (hgc.norm.pow 2), ⟨K * M ^ 2, fun θ => ?_⟩, fun θ => ?_⟩
  · rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (hK _ (hhab θ)) (pow_le_pow_left₀ (norm_nonneg _) (hM θ) 2) (by positivity)
      ((norm_nonneg _).trans (hK _ (hhab θ)))
  · exact mul_nonneg (hΦ.2.1 _ (hab (hhab θ))).le (sq_nonneg _)

/-- Gaussian part: the conditional Φ-entropy given `X = x`. -/
lemma phiEnt_outKernel_le {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) (hG : PhiSobBayes.PhiSobolev γₙ J Φ 1)
    {a b : ℝ} (hab : Icc a b ⊆ J) (h : E → ℝ) (hh : ContDiff ℝ 1 h)
    (hhab : ∀ x, h x ∈ Icc a b) {M : ℝ} (hM : ∀ x, ‖gradient h x‖ ≤ M) {t : ℝ} (ht : 0 < t)
    (x : E) :
    PhiSobBayes.phiEnt (outKernel t x) Φ h ≤
      t / 2 * ∫ g, deriv (deriv Φ) (h (t • x + Real.sqrt t • g)) *
        ‖gradient h (t • x + Real.sqrt t • g)‖ ^ 2 ∂γₙ := by
  obtain ⟨hΦc, -⟩ := admissible_contOn hJ hΦ
  have hΦh : Continuous (fun x => Φ (h x)) :=
    hΦc.comp_continuous hh.continuous fun x => hab (hhab x)
  have e : PhiSobBayes.phiEnt (outKernel t x) Φ h =
      PhiSobBayes.phiEnt γₙ Φ (fun g => h (t • x + Real.sqrt t • g)) := by
    unfold PhiSobBayes.phiEnt
    rw [integral_outKernel t x _ hΦh, integral_outKernel t x _ hh.continuous]
  have hd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hgr : ∀ g, gradient (fun g => h (t • x + Real.sqrt t • g)) g =
      Real.sqrt t • gradient h (t • x + Real.sqrt t • g) :=
    fun g => gradient_comp_affine h hd _ _ _
  have := phiSobolev_extend γₙ hJ hΦ hG hab (fun g => h (t • x + Real.sqrt t • g))
    (hh.comp (by fun_prop)) (fun g => hhab _) ⟨Real.sqrt t * M, fun g => by
      rw [hgr, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hM _) (Real.sqrt_nonneg _)⟩
  rw [e]
  refine this.trans (le_of_eq ?_)
  simp_rw [hgr, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ht.le]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; funext g; ring


/-! ### The conditional mean `H x = E h(t x + √t G)` -/

/-- `H x = ∫ h(t x + √t g) dγ(g)`, the mean of `h` under `outKernel t x` -/
def Hfun (t : ℝ) (h : E → ℝ) (x : E) : ℝ := ∫ g, h (t • x + Real.sqrt t • g) ∂γₙ

lemma Hfun_eq (t : ℝ) (h : E → ℝ) (hh : Continuous h) (x : E) :
    Hfun t h x = ∫ θ, h θ ∂(outKernel t x) := (integral_outKernel t x h hh).symm

lemma hasFDerivAt_Hfun (h : E → ℝ) (hh : ContDiff ℝ 1 h) {K : ℝ} (hK : ∀ x, ‖h x‖ ≤ K)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ h x‖ ≤ M) (t : ℝ) (x : E) :
    HasFDerivAt (Hfun t h) (∫ g, t • fderiv ℝ h (t • x + Real.sqrt t • g) ∂γₙ) x := by
  have hd := hh.differentiable one_ne_zero
  have hdc := hh.continuous_fderiv one_ne_zero
  show HasFDerivAt (fun x => ∫ g, h (t • x + Real.sqrt t • g) ∂γₙ) _ x
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun _ => |t| * M)
    (F := fun y g => h (t • y + Real.sqrt t • g))
    (F' := fun y g => t • fderiv ℝ h (t • y + Real.sqrt t • g)) univ_mem
    (Eventually.of_forall fun y => (hh.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_of_cont_bdd _ _ (hh.continuous.comp (by fun_prop)) K (fun g => hK _))
    (((hdc.comp (by fun_prop)).const_smul t).aestronglyMeasurable)
    (ae_of_all _ fun g y _ => ?_) (integrable_const _) (ae_of_all _ fun g y _ => ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  · refine ((hd _).hasFDerivAt.comp y
      (((hasFDerivAt_id y).const_smul t).add_const _)).congr_fderiv ?_
    ext v; simp

lemma fderiv_Hfun (h : E → ℝ) (hh : ContDiff ℝ 1 h) {K : ℝ} (hK : ∀ x, ‖h x‖ ≤ K)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ h x‖ ≤ M) (t : ℝ) :
    fderiv ℝ (Hfun t h) = fun x => ∫ g, t • fderiv ℝ h (t • x + Real.sqrt t • g) ∂γₙ :=
  funext fun x => (hasFDerivAt_Hfun h hh hK hM t x).fderiv

lemma contDiff_Hfun (h : E → ℝ) (hh : ContDiff ℝ 1 h) {K : ℝ} (hK : ∀ x, ‖h x‖ ≤ K)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ h x‖ ≤ M) (t : ℝ) : ContDiff ℝ 1 (Hfun t h) := by
  have hdc := hh.continuous_fderiv one_ne_zero
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_Hfun h hh hK hM t x).differentiableAt, ?_⟩
  rw [fderiv_Hfun h hh hK hM t]
  refine continuous_of_dominated (bound := fun _ => |t| * M)
    (fun x => ((hdc.comp (by fun_prop)).const_smul t).aestronglyMeasurable)
    (fun x => ae_of_all _ fun g => ?_) (integrable_const _)
    (ae_of_all _ fun g => (hdc.comp (by fun_prop)).const_smul t)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)

lemma norm_gradient_Hfun_le (h : E → ℝ) (hh : ContDiff ℝ 1 h) {K : ℝ} (hK : ∀ x, ‖h x‖ ≤ K)
    {M : ℝ} (hM : ∀ x, ‖gradient h x‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    ‖gradient (Hfun t h) x‖ ≤ t * ∫ g, ‖gradient h (t • x + Real.sqrt t • g)‖ ∂γₙ := by
  have hM' : ∀ x, ‖fderiv ℝ h x‖ ≤ M := fun x => (ext_norm_gradient h x) ▸ hM x
  rw [ext_norm_gradient, fderiv_Hfun h hh hK hM' t]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← integral_const_mul]
  congr 1; funext g
  rw [norm_smul, Real.norm_of_nonneg ht, ext_norm_gradient]

lemma Hfun_mem (h : E → ℝ) (hh : Continuous h) {a b : ℝ} (hhab : ∀ x, h x ∈ Icc a b)
    (t : ℝ) (x : E) : Hfun t h x ∈ Icc a b :=
  integral_mem_Icc _ _ (hh.comp (by fun_prop)).aestronglyMeasurable fun g => hhab _


/-- Prior part: the Φ-entropy of the conditional mean under `μ`. -/
lemma phiEnt_Hfun_le (μ : Measure E) [IsProbabilityMeasure μ]
    {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) {C : ℝ} (hC : 0 ≤ C)
    (hS : PhiSobBayes.PhiSobolev μ J Φ C)
    {a b : ℝ} (hab : Icc a b ⊆ J) (h : E → ℝ) (hh : ContDiff ℝ 1 h)
    (hhab : ∀ x, h x ∈ Icc a b) {M : ℝ} (hM : ∀ x, ‖gradient h x‖ ≤ M) {t : ℝ} (ht : 0 < t) :
    PhiSobBayes.phiEnt μ Φ (Hfun t h) ≤
      C / 2 * (t ^ 2 * ∫ x, ∫ g, deriv (deriv Φ) (h (t • x + Real.sqrt t • g)) *
        ‖gradient h (t • x + Real.sqrt t • g)‖ ^ 2 ∂γₙ ∂μ) := by
  have hab' : a ≤ b := (hhab 0).1.trans (hhab 0).2
  have hK : ∀ x, ‖h x‖ ≤ max |a| |b| := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · nlinarith [le_max_left |a| |b|, neg_abs_le a, (hhab x).1]
    · nlinarith [le_max_right |a| |b|, le_abs_self b, (hhab x).2]
  have hM' : ∀ x, ‖fderiv ℝ h x‖ ≤ M := fun x => (ext_norm_gradient h x) ▸ hM x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨hFc, ⟨KF, hKF⟩, hF0⟩ := integrand_facts hJ hΦ hab h hh hhab hM
  have h1 := phiSobolev_extend μ hJ hΦ hS hab (Hfun t h) (contDiff_Hfun h hh hK hM' t)
    (Hfun_mem h hh.continuous hhab t) ⟨t * M, fun x => by
      refine (norm_gradient_Hfun_le h hh hK hM ht.le x).trans
        (mul_le_mul_of_nonneg_left ?_ ht.le)
      calc ∫ g, ‖gradient h (t • x + Real.sqrt t • g)‖ ∂γₙ ≤ ∫ _g, M ∂γₙ :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _)
              (ae_of_all _ fun _ => hM _)
        _ = M := by simp⟩
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← integral_const_mul]
  have hint : Integrable (fun p : E × E => deriv (deriv Φ) (h (t • p.1 + Real.sqrt t • p.2)) *
      ‖gradient h (t • p.1 + Real.sqrt t • p.2)‖ ^ 2) (μ.prod γₙ) :=
    integrable_of_cont_bdd _ _ (hFc.comp (by fun_prop)) KF (fun p => hKF _)
  refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) (hint.integral_prod_left.const_mul _)
    (ae_of_all _ fun x => ?_)
  · exact mul_nonneg (hΦ.2.1 _ (hab (Hfun_mem h hh.continuous hhab t x))).le (sq_nonneg _)
  · have hj := phi_jensen γₙ hJ hΦ hab (fun g => h (t • x + Real.sqrt t • g))
      (hh.continuous.comp (by fun_prop)).measurable (fun g => hhab _)
      (fun g => ‖gradient h (t • x + Real.sqrt t • g)‖)
      ((continuous_gradient_of_contDiff h hh).norm.comp (by fun_prop)).measurable
      ⟨M, fun g => by rw [abs_norm]; exact hM _⟩
    simp only [abs_norm] at hj
    have hg := norm_gradient_Hfun_le h hh hK hM ht.le x
    have hψ0 : 0 ≤ deriv (deriv Φ) (Hfun t h x) :=
      (hΦ.2.1 _ (hab (Hfun_mem h hh.continuous hhab t x))).le
    calc deriv (deriv Φ) (Hfun t h x) * ‖gradient (Hfun t h) x‖ ^ 2
        ≤ deriv (deriv Φ) (Hfun t h x) *
            (t * ∫ g, ‖gradient h (t • x + Real.sqrt t • g)‖ ∂γₙ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg 2) hψ0
      _ = t ^ 2 * (deriv (deriv Φ) (Hfun t h x) *
            (∫ g, ‖gradient h (t • x + Real.sqrt t • g)‖ ∂γₙ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hj (sq_nonneg t)


/-! ### Main theorem -/

/-- **Φ-Sobolev inequality for the output law** `Qt μ t` (law of `t X + √t G`), by tensorization
of the prior inequality (constant `C`) and the Gaussian one (constant `1`). -/
theorem phiSobolev_Qt {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ} (hΦ : PhiSobBayes.AdmissiblePhi J Φ)
    {C : ℝ} (hC : 0 ≤ C) (hS : PhiSobBayes.PhiSobolev μ J Φ C)
    (hG : PhiSobBayes.PhiSobolev (stdGaussian (EuclideanSpace ℝ (Fin n))) J Φ 1)
    {a b : ℝ} (hab : Set.Icc a b ⊆ J) (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ 1 h)
    (hhab : ∀ x, h x ∈ Set.Icc a b) (hgrad : ∃ M, ∀ x, ‖gradient h x‖ ≤ M) (t : ℝ) (ht : 0 < t) :
    PhiSobBayes.phiEnt (Qt μ t) Φ h ≤
      (C * t ^ 2 + t) / 2 * ∫ θ, deriv (deriv Φ) (h θ) * ‖gradient h θ‖ ^ 2 ∂(Qt μ t) := by
  obtain ⟨M, hM⟩ := hgrad
  obtain ⟨hΦc, -⟩ := admissible_contOn hJ hΦ
  obtain ⟨hFc, ⟨KF, hKF⟩, hF0⟩ := integrand_facts hJ hΦ hab h hh hhab hM
  have := isProb_Qt (π := μ) t
  have hconv : ConvexOn ℝ J Φ := by
    have hd1 : ContDiffOn ℝ ∞ (deriv Φ) J := hΦ.1.deriv_of_isOpen hJ.1 (by simp)
    exact convexOn_of_deriv2_nonneg' hJ.2.1.convex (hΦ.1.differentiableOn (by simp))
      (hd1.differentiableOn (by simp)) (fun z hz => by simpa using (hΦ.2.1 z hz).le)
  have hΦh : Continuous (fun x => Φ (h x)) :=
    hΦc.comp_continuous hh.continuous fun x => hab (hhab x)
  have hK : ∀ x, ‖h x‖ ≤ max |a| |b| := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · nlinarith [le_max_left |a| |b|, neg_abs_le a, (hhab x).1]
    · nlinarith [le_max_right |a| |b|, le_abs_self b, (hhab x).2]
  obtain ⟨KΦ, hKΦ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hΦc.mono hab)
  have hA := PhiSobBayes.lemma_A_19 μ (outKernel t) J hJ.2.1 Φ hconv h (fun x => hab (hhab x))
    (by rw [bind_outKernel]; exact integrable_of_cont_bdd _ _ hh.continuous _ hK)
    (by rw [bind_outKernel]; exact integrable_of_cont_bdd _ _ hΦh _ fun x => hKΦ _ (hhab x))
  rw [bind_outKernel] at hA
  have hH : (fun y => ∫ x, h x ∂(outKernel t y)) = Hfun t h :=
    funext fun y => (Hfun_eq t h hh.continuous y).symm
  rw [hH] at hA
  rw [hA, integral_Qt_iter μ t _ hFc KF hKF]
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => deriv (deriv Φ) (h (t • p.1 + Real.sqrt t • p.2)) *
      ‖gradient h (t • p.1 + Real.sqrt t • p.2)‖ ^ 2) (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
    integrable_of_cont_bdd _ _ (hFc.comp (by fun_prop)) KF (fun p => hKF _)
  set I := ∫ x, ∫ g, deriv (deriv Φ) (h (t • x + Real.sqrt t • g)) *
      ‖gradient h (t • x + Real.sqrt t • g)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => integral_nonneg fun g => hF0 _
  have h1 : ∫ y, PhiSobBayes.phiEnt (outKernel t y) Φ h ∂μ ≤ t / 2 * I := by
    by_cases hi : Integrable (fun y => PhiSobBayes.phiEnt (outKernel t y) Φ h) μ
    · rw [hI, ← integral_const_mul]
      exact integral_mono hi (hint.integral_prod_left.const_mul _)
        (fun y => phiEnt_outKernel_le hJ hΦ hG hab h hh hhab hM ht y)
    · rw [integral_undef hi]; positivity
  have h2 := phiEnt_Hfun_le μ hJ hΦ hC hS hab h hh hhab hM ht
  calc _ ≤ t / 2 * I + C / 2 * (t ^ 2 * I) := add_le_add h1 h2
    _ = _ := by ring

end PSBSL

end
end

-- ===== FwdMono.lean =====
section

/-! Comparison lemma: if `K` is continuous on `[s₀,T]` (`0 < s₀`) and
`∫_{s₁}^{s₂} K s / (s (1 + C s)) ds ≤ K s₂ - K s₁` for all `s₀ ≤ s₁ ≤ s₂ ≤ T`, then
`K s₀ (1 + C s₀)/s₀ ≤ K T (1 + C T)/T`. -/

set_option autoImplicit false

open MeasureTheory intervalIntegral

noncomputable section

namespace PSBSL

theorem fwd_mono {C s₀ T : ℝ} (hC : 0 ≤ C) (hs₀ : 0 < s₀) (hT : s₀ ≤ T) (K : ℝ → ℝ)
    (hK : ContinuousOn K (Set.Icc s₀ T))
    (hineq : ∀ s₁ s₂, s₀ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ T →
      ∫ s in s₁..s₂, K s / (s * (1 + C * s)) ≤ K s₂ - K s₁) :
    K s₀ * ((1 + C * s₀) / s₀) ≤ K T * ((1 + C * T) / T) := by
  set c : ℝ → ℝ := fun s => 1 / (s * (1 + C * s)) with hc
  have hpos : ∀ s ∈ Set.Icc s₀ T, 0 < s * (1 + C * s) := fun s hs => by
    have : 0 < s := hs₀.trans_le hs.1
    positivity
  have hcK : ContinuousOn (fun s => K s / (s * (1 + C * s))) (Set.Icc s₀ T) :=
    hK.div (continuousOn_id.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id)))
      (fun s hs => (hpos s hs).ne')
  set M : ℝ → ℝ := fun s => K s₀ + ∫ r in s₀..s, K r / (r * (1 + C * r)) with hM
  have hKM : ∀ s ∈ Set.Icc s₀ T, M s ≤ K s := by
    intro s hs
    have := hineq s₀ s le_rfl hs.1 hs.2
    simp only [hM]; linarith
  set E : ℝ → ℝ := fun s => (1 + C * s) / s with hE
  -- g = M * E is monotone on [s₀, T]
  have hMcont : ContinuousOn M (Set.Icc s₀ T) := by
    have : ContinuousOn (fun s => ∫ r in s₀..s, K r / (r * (1 + C * r))) (Set.Icc s₀ T) := by
      have hii : IntegrableOn (fun r => K r / (r * (1 + C * r))) (Set.uIcc s₀ T) volume := by
        rw [Set.uIcc_of_le hT]; exact hcK.integrableOn_compact isCompact_Icc
      intro s hs
      have := (intervalIntegral.continuousOn_primitive_interval (μ := volume) hii)
      rw [Set.uIcc_of_le hT] at this
      exact (this s hs)
    exact continuousOn_const.add this
  have hEcont : ContinuousOn E (Set.Icc s₀ T) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).div continuousOn_id
      (fun s hs => (hs₀.trans_le hs.1).ne')
  have hderiv : ∀ s ∈ interior (Set.Icc s₀ T),
      HasDerivAt (fun s => M s * E s)
        (K s / (s * (1 + C * s)) * E s + M s * (-1 / s ^ 2)) s := by
    intro s hs
    rw [interior_Icc] at hs
    have hs0 : 0 < s := hs₀.trans hs.1
    have hM' : HasDerivAt M (K s / (s * (1 + C * s))) s := by
      have hcont : ContinuousAt (fun r => K r / (r * (1 + C * r))) s :=
        hcK.continuousAt (Icc_mem_nhds hs.1 hs.2)
      have hii : IntervalIntegrable (fun r => K r / (r * (1 + C * r))) volume s₀ s :=
        (hcK.mono (by rw [Set.uIcc_of_le hs.1.le]; exact Set.Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable
      have hmeas : StronglyMeasurableAtFilter (fun r => K r / (r * (1 + C * r))) (nhds s) volume :=
        (hcK.mono (Set.Ioo_subset_Icc_self)).stronglyMeasurableAtFilter isOpen_Ioo s hs
      exact (intervalIntegral.integral_hasDerivAt_right hii hmeas hcont).const_add (K s₀)
    have hE' : HasDerivAt E (-1 / s ^ 2) s := by
      have h1 : HasDerivAt (fun s : ℝ => s⁻¹ + C) (-1 / s ^ 2) s := by
        rw [show (-1 / s ^ 2 : ℝ) = -(s ^ 2)⁻¹ by ring]
        exact (hasDerivAt_inv hs0.ne').add_const C
      apply h1.congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hs0] with r hr
      simp only [hE]; field_simp
    exact hM'.mul hE'
  have hmono : MonotoneOn (fun s => M s * E s) (Set.Icc s₀ T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s₀ T) (hMcont.mul hEcont)
    · intro s hs; exact (hderiv s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      have hd := (hderiv s hs).deriv
      show 0 ≤ deriv (fun s => M s * E s) s
      rw [hd]
      have hs' := interior_subset hs
      have hs0 : 0 < s := hs₀.trans_le hs'.1
      have h1 : 0 < 1 + C * s := by positivity
      have hkm := hKM s hs'
      have e : K s / (s * (1 + C * s)) * E s + M s * (-1 / s ^ 2) = (K s - M s) / s ^ 2 := by
        simp only [hE]; field_simp; ring
      rw [e]; exact div_nonneg (by linarith) (by positivity)
  have h1 := hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  simp only at h1
  have hM0 : M s₀ = K s₀ := by simp [hM]
  rw [hM0] at h1
  have hET : 0 < E T := by simp only [hE]; have : 0 < T := hs₀.trans_le hT; positivity
  calc K s₀ * ((1 + C * s₀) / s₀) = K s₀ * E s₀ := rfl
    _ ≤ M T * E T := h1
    _ ≤ K T * E T := mul_le_mul_of_nonneg_right (hKM T ⟨hT, le_rfl⟩) hET.le
    _ = K T * ((1 + C * T) / T) := rfl

end PSBSL

end
end

-- ===== Translate.lean =====
section

/-! Translation between the paper's `y`-parametrization (`posterior`, `gamObs`) and the natural
parametrization `θ = √t • y` (`post`, `Qt`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace PSBSL

variable {n : ℕ}

lemma exp_paper_eq (t : ℝ) (ht : 0 ≤ t) (y x : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2) =
      Real.exp (-‖y‖ ^ 2 / 2) * wt t (Real.sqrt t • y) x := by
  unfold wt
  rw [← Real.exp_add]
  congr 1
  have h1 : ‖y - Real.sqrt t • x‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, Real.sqrt t • x⟫ + ‖Real.sqrt t • x‖ ^ 2 :=
    norm_sub_sq_real y _
  have h2 : ‖Real.sqrt t • x‖ ^ 2 = t * ‖x‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht]
  rw [h1, h2, inner_smul_right, inner_smul_left]
  simp only [RCLike.conj_to_real]
  ring

lemma posterior_eq_post (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) (ht : 0 ≤ t)
    (y : EuclideanSpace ℝ (Fin n)) :
    PhiSobBayes.posterior μ t y = post μ t (Real.sqrt t • y) := by
  unfold PhiSobBayes.posterior post Zt
  congr 1
  funext x
  simp_rw [exp_paper_eq t ht y]
  rw [integral_const_mul]
  congr 1
  have hc : 0 < Real.exp (-‖y‖ ^ 2 / 2) := Real.exp_pos _
  rw [mul_div_mul_left _ _ hc.ne']

lemma gamObs_eq_map_Qt (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) (ht : 0 < t) :
    PhiSobBayes.gamObs μ t = (Qt μ t).map (fun θ => (Real.sqrt t)⁻¹ • θ) := by
  unfold PhiSobBayes.gamObs Qt
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp_apply, smul_add, smul_smul]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have e1 : (Real.sqrt t)⁻¹ * t = Real.sqrt t := by
    have := Real.mul_self_sqrt ht.le
    field_simp
    linarith
  rw [e1, inv_mul_cancel₀ hs.ne', one_smul]

end PSBSL

end
end

-- ===== Cov.lean =====
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section
namespace PSBSL
variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma cov_line_hasDerivAt (W : E → ℝ) (hW1 : Differentiable ℝ W) (x v : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => W (x + s • v)) (fderiv ℝ W (x + s • v) v) s := by
  have h : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  exact (hW1 _).hasFDerivAt.comp_hasDerivAt s h

lemma cov_line_hasDerivAt2 (W : E → ℝ) (hW2 : Differentiable ℝ (fderiv ℝ W)) (x v : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ W (x + s • v) v)
      (fderiv ℝ (fderiv ℝ W) (x + s • v) v v) s := by
  have h : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have := (hW2 _).hasFDerivAt.comp_hasDerivAt s h
  exact this.clm_apply (hasDerivAt_const s v) |>.congr_deriv (by simp)

lemma cov_sq_line_hasDerivAt (x v : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ‖x + s • v‖ ^ 2 / 2) (⟪x + s • v, v⟫) s := by
  have h : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  exact ((h.norm_sq).div_const 2).congr_deriv (by ring)

lemma cov_inner_line_hasDerivAt (x v : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪x + s • v, v⟫) (‖v‖ ^ 2) s := by
  have h : HasDerivAt (fun s : ℝ => ⟪x, v⟫ + s * ‖v‖ ^ 2) (‖v‖ ^ 2) s := by
    simpa using ((hasDerivAt_id s).mul_const (‖v‖ ^ 2)).const_add ⟪x, v⟫
  convert h using 1
  funext s
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- the convex part of a strongly log-concave potential -/
lemma slc_line_convex (W : E → ℝ) (κ : ℝ) (hW1 : Differentiable ℝ W)
    (hW2 : Differentiable ℝ (fderiv ℝ W))
    (hW3 : ∀ x v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W) x v v) (x v : E) :
    ConvexOn ℝ univ (fun s : ℝ => W (x + s • v) - κ * (‖x + s • v‖ ^ 2 / 2)) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (f' := fun s => fderiv ℝ W (x + s • v) v - κ * ⟪x + s • v, v⟫)
    (f'' := fun s => fderiv ℝ (fderiv ℝ W) (x + s • v) v v - κ * ‖v‖ ^ 2) ?_ ?_ ?_ ?_
  · refine continuousOn_of_forall_continuousAt (fun s _ => ?_)
    exact ((cov_line_hasDerivAt W hW1 x v s).sub
      ((cov_sq_line_hasDerivAt x v s).const_mul κ)).continuousAt
  · intro s _
    exact ((cov_line_hasDerivAt W hW1 x v s).sub
      ((cov_sq_line_hasDerivAt x v s).const_mul κ)).hasDerivWithinAt
  · intro s _
    exact ((cov_line_hasDerivAt2 W hW2 x v s).sub
      ((cov_inner_line_hasDerivAt x v s).const_mul κ)).hasDerivWithinAt
  · intro s _
    have := hW3 (x + s • v) v
    linarith

theorem slc_convex (W : E → ℝ) (κ : ℝ) (hW1 : Differentiable ℝ W)
    (hW2 : Differentiable ℝ (fderiv ℝ W))
    (hW3 : ∀ x v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W) x v v) :
    ConvexOn ℝ univ (fun x : E => W x - κ * ‖x‖ ^ 2 / 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hc := (slc_line_convex W κ hW1 hW2 hW3 x (y - x)).2 (mem_univ (0:ℝ)) (mem_univ (1:ℝ))
    ha hb hab
  have e1 : a • x + b • y = x + (a • (0:ℝ) + b • (1:ℝ)) • (y - x) := by
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one]
    obtain rfl : a = 1 - b := by linarith
    module
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at hc
  rw [e1]
  simp only [smul_eq_mul] at hc ⊢
  linarith

theorem slc_quadratic_lower (W : E → ℝ) (κ : ℝ) (hW1 : Differentiable ℝ W)
    (hW2 : Differentiable ℝ (fderiv ℝ W))
    (hW3 : ∀ x v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W) x v v) (x y : E) :
    W x + fderiv ℝ W x (y - x) + κ / 2 * ‖y - x‖ ^ 2 ≤ W y := by
  have hc := slc_line_convex W κ hW1 hW2 hW3 x (y - x)
  have hd := (cov_line_hasDerivAt W hW1 x (y - x) 0).sub
      ((cov_sq_line_hasDerivAt x (y - x) 0).const_mul κ)
  have := hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero, div_one] at this
  have h2 : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
    have : y = x + (y - x) := by abel
    conv_lhs => rw [this]
    rw [norm_add_sq_real]
  rw [h2] at this
  nlinarith
/-! ## (C2) integrability -/

lemma cov_gauss_integrable (b : ℝ) (hb : 0 < b) (w : E) :
    Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2 + ⟪w, x⟫)) volume := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (b : ℂ))
    (by simpa using hb) 1 w).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

lemma slc_integrable_exp_quad {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (θ : E) (a : ℝ) (ha : a < κ / 2) :
    Integrable (fun x => Real.exp (⟪θ, x⟫ + a * ‖x‖ ^ 2)) μ := by
  obtain ⟨_, W, h1, h2, h3, rfl⟩ := hμ
  have hWc : Continuous W := h1.continuous
  have hm : Measurable fun x : E => ENNReal.ofReal (Real.exp (-W x)) :=
    hWc.neg.rexp.measurable.ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  set g0 : E := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ W 0)
  have hG := (cov_gauss_integrable (κ / 2 - a) (by linarith) (θ - g0)).const_mul (Real.exp (-W 0))
  refine hG.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hm.ennreal_toReal.smul
      (by fun_prop : Continuous fun x : E => Real.exp (⟪θ, x⟫ + a * ‖x‖ ^ 2)).measurable)
      |>.aestronglyMeasurable
  · have hq := slc_quadratic_lower W κ h1 h2 h3 0 x
    have hg0 : fderiv ℝ W 0 x = ⟪g0, x⟫ := by
      simp [g0, InnerProductSpace.toDual_symm_apply]
    simp only [sub_zero, hg0] at hq
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, inner_sub_left]
    nlinarith

theorem slc_integrable_exp_inner {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) : Integrable (fun x => Real.exp ⟪θ, x⟫) μ := by
  simpa using slc_integrable_exp_quad hμ θ 0 (by linarith)

lemma cov_norm_pow_le_exp (k : ℕ) (c : ℝ) (hc : 0 < c) (x : E) :
    ‖x‖ ^ k ≤ 1 + (k.factorial / c ^ k) * Real.exp (c * ‖x‖ ^ 2) := by
  have h1 : ‖x‖ ^ k ≤ 1 + (‖x‖ ^ 2) ^ k := by
    rcases le_or_gt ‖x‖ 1 with h | h
    · have := pow_le_one₀ (norm_nonneg x) h (n := k)
      have : 0 ≤ (‖x‖ ^ 2) ^ k := by positivity
      linarith
    · rw [← pow_mul]
      have := pow_le_pow_right₀ h.le (by omega : k ≤ 2 * k)
      linarith
  have h2 := Real.pow_div_factorial_le_exp (c * ‖x‖ ^ 2) (by positivity) k
  have hck : 0 < c ^ k := by positivity
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [mul_pow, div_le_iff₀ hf] at h2
  have h3 : (‖x‖ ^ 2) ^ k ≤ k.factorial / c ^ k * Real.exp (c * ‖x‖ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hck]
    linarith
  linarith

theorem slc_integrable_pow {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (k : ℕ) : Integrable (fun x => ‖x‖ ^ k) μ := by
  have := hμ.1
  have hI := (integrable_const (1 : ℝ)).add ((slc_integrable_exp_quad hμ 0 (κ / 4)
    (by linarith)).const_mul (k.factorial / (κ / 4) ^ k))
  refine hI.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa using cov_norm_pow_le_exp k (κ / 4) (by linarith) x

theorem slc_integrable_id {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) : Integrable (fun x : E => x) μ := by
  have := slc_integrable_pow hμ hκ 1
  simp only [pow_one] at this
  exact (integrable_norm_iff (by fun_prop)).mp this
/-! ## (C7) posteriors are strongly log-concave -/

lemma cov_post_hasFDerivAt_q (t : ℝ) (θ x : E) :
    HasFDerivAt (fun x : E => -⟪θ, x⟫ + t * ‖x‖ ^ 2 / 2) (innerSL ℝ (t • x - θ)) x := by
  have h1 : HasFDerivAt (fun x : E => -⟪θ, x⟫) (-(innerSL ℝ θ)) x :=
    ((innerSL ℝ θ).hasFDerivAt (x := x)).neg
  have h2 := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq.const_mul (t / 2))
  have h := h1.add h2
  have hfun : (fun x : E => -⟪θ, x⟫ + t * ‖x‖ ^ 2 / 2) =
      fun x => -⟪θ, x⟫ + t / 2 * ‖id x‖ ^ 2 := by
    funext z; simp only [id]; ring
  rw [hfun]
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

lemma cov_post_hasFDerivAt_lin (t : ℝ) (θ x : E) :
    HasFDerivAt (fun x : E => innerSL ℝ (t • x - θ)) (t • innerSL ℝ) x := by
  have := ((t • innerSL ℝ : E →L[ℝ] _).hasFDerivAt (x := x)).sub_const (innerSL ℝ θ)
  have hfun : (fun x : E => innerSL ℝ (t • x - θ)) =
      fun x => (t • innerSL ℝ : E →L[ℝ] _) x - innerSL ℝ θ := by
    funext z
    simp [map_sub, map_smul]
  rw [hfun]
  exact this

lemma cov_wt_eq (t : ℝ) (θ x : E) :
    wt t θ x = Real.exp (⟪θ, x⟫ + (-t / 2) * ‖x‖ ^ 2) := by
  unfold wt; congr 1; ring

theorem slc_integrable_wt {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => wt t θ x) μ := by
  simp_rw [cov_wt_eq]
  exact slc_integrable_exp_quad hμ θ _ (by linarith)

theorem slc_Zt_pos {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) (t : ℝ) (ht : 0 ≤ t) : 0 < Zt μ t θ := by
  have := hμ.1
  exact integral_exp_pos (slc_integrable_wt hμ hκ θ t ht)

theorem post_slc {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) (t : ℝ) (ht : 0 ≤ t) :
    PhiSobBayes.IsStronglyLogConcave (post μ t θ) (κ + t) := by
  have hint := slc_integrable_wt hμ hκ θ t ht
  have hZpos := slc_Zt_pos hμ hκ θ t ht
  set Z := Zt μ t θ with hZ
  obtain ⟨hprob, V, hV1, hV2, hV3, rfl⟩ := hμ
  set μ0 := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) with hμ0
  have hgc : Continuous fun x => wt t θ x := by unfold wt; fun_prop
  have hpost : post μ0 t θ = μ0.withDensity (fun x => ENNReal.ofReal (wt t θ x / Z)) := rfl
  rw [hpost]
  refine ⟨?_, fun x => V x + ((-⟪θ, x⟫ + t * ‖x‖ ^ 2 / 2) + Real.log Z), ?_⟩
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_div, ← Zt, ← hZ, div_self hZpos.ne', ENNReal.ofReal_one]
    · exact hint.div_const Z
    · exact Filter.Eventually.of_forall (fun x => by unfold wt; positivity)
  have hfd : fderiv ℝ (fun x => V x + ((-⟪θ, x⟫ + t * ‖x‖ ^ 2 / 2) + Real.log Z)) =
      fun x => fderiv ℝ V x + innerSL ℝ (t • x - θ) := by
    funext x
    exact ((hV1 x).hasFDerivAt.add ((cov_post_hasFDerivAt_q t θ x).add_const _)).fderiv
  have hfd2 := fun x => (hV2 x).hasFDerivAt.add (cov_post_hasFDerivAt_lin t θ x)
  refine ⟨fun x => ((hV1 x).hasFDerivAt.add
      ((cov_post_hasFDerivAt_q t θ x).add_const _)).differentiableAt, ?_, ?_, ?_⟩
  · rw [hfd]; exact fun x => (hfd2 x).differentiableAt
  · intro x v
    rw [hfd, show (fun x => fderiv ℝ V x + innerSL ℝ (t • x - θ)) =
      (fderiv ℝ V + fun x => innerSL ℝ (t • x - θ)) from rfl, (hfd2 x).fderiv]
    have := hV3 x v
    simp
    have h3 : ((innerSL ℝ) v) v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    erw [h3]
    linarith
  · rw [hμ0, ← withDensity_mul]
    · congr 1
      funext x
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      unfold wt
      rw [show -(V x + ((-⟪θ, x⟫ + t * ‖x‖ ^ 2 / 2) + Real.log Z)) =
        (-V x + (⟪θ, x⟫ - t * ‖x‖ ^ 2 / 2)) - Real.log Z by ring]
      rw [Real.exp_sub _ (Real.log Z), Real.exp_add (-V x), Real.exp_log hZpos]; ring
    · exact (hV1.continuous.neg.rexp).measurable.ennreal_ofReal
    · exact ((hgc).measurable.div_const Z).ennreal_ofReal
/-! ## (C3) concavity of the log-Laplace transform minus `‖θ‖²/(2κ)` -/

/-- log-Laplace transform `Λ(θ) = log ∫ exp ⟪θ, x⟫ dμ` -/
def logLap (μ : Measure E) (θ : E) : ℝ := Real.log (∫ x, Real.exp ⟪θ, x⟫ ∂μ)

lemma cov_logConcaveOn_log_concave {F : E → ℝ} (hpos : ∀ θ, 0 < F θ)
    (hF : ConvexOptimization.LogConcaveOn univ F) :
    ConcaveOn ℝ univ (fun θ => Real.log (F θ)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := hF.2 x (mem_univ _) y (mem_univ _) a b ha hb hab
  have h' := Real.log_le_log (by have := hpos x; have := hpos y; positivity) h
  rw [Real.log_mul (Real.rpow_pos_of_pos (hpos x) a).ne' (Real.rpow_pos_of_pos (hpos y) b).ne',
    Real.log_rpow (hpos x), Real.log_rpow (hpos y)] at h'
  simpa [smul_eq_mul] using h'

lemma cov_norm_sq_convex_comb (z w : E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • z + b • w‖ ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
  have e : ‖a • z + b • w‖ ^ 2 = a ^ 2 * ‖z‖ ^ 2 + 2 * (a * b) * ⟪z, w⟫ + b ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    ring
  have h0 := norm_sub_sq_real z w
  have h1 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg ‖z - w‖)
  obtain rfl : b = 1 - a := by linarith
  rw [e]
  nlinarith

theorem slc_logLaplace_concave {μ : Measure E} {κ : ℝ}
    (hμ : PhiSobBayes.IsStronglyLogConcave μ κ) (hκ : 0 < κ) :
    ConcaveOn ℝ univ (fun θ => logLap μ θ - ‖θ‖ ^ 2 / (2 * κ)) := by
  have hμ' := hμ
  obtain ⟨_, V, h1, h2, h3, hμeq⟩ := hμ'
  have hVc : Continuous V := h1.continuous
  set U : E → ℝ := fun x => V x - κ * ‖x‖ ^ 2 / 2 with hU
  have hUconv : ConvexOn ℝ univ U := slc_convex V κ h1 h2 h3
  have hUc : Continuous U := by simp only [hU]; fun_prop
  set f : E × E → ℝ := fun p => Real.exp (-(κ * ‖p.2‖ ^ 2 / 2) - U (p.2 + κ⁻¹ • p.1)) with hf
  have hfc : Continuous f := by simp only [hf]; fun_prop
  -- pointwise identity
  have hpt : ∀ θ z : E, Real.exp (-V (z + κ⁻¹ • θ)) * Real.exp ⟪θ, z + κ⁻¹ • θ⟫ =
      Real.exp (‖θ‖ ^ 2 / (2 * κ)) * f (θ, z) := by
    intro θ z
    simp only [hf, hU, ← Real.exp_add]
    congr 1
    rw [norm_add_sq_real, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ),
      real_inner_comm z θ]
    field_simp
    ring
  have hdens : Measurable fun x : E => ENNReal.ofReal (Real.exp (-V x)) :=
    hVc.neg.rexp.measurable.ennreal_ofReal
  -- integrability of the sections
  have hfint : ∀ θ : E, Integrable (fun z : E => f (θ, z)) := by
    intro θ
    have hI := slc_integrable_exp_inner hμ hκ θ
    rw [hμeq, integrable_withDensity_iff_integrable_smul' hdens
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hI
    have := (hI.comp_add_right (κ⁻¹ • θ)).const_mul (Real.exp (-(‖θ‖ ^ 2 / (2 * κ))))
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    rw [hpt, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  set F : E → ℝ := fun θ => ∫ z, f (θ, z) with hF
  have hFpos : ∀ θ, 0 < F θ := fun θ => integral_exp_pos (hfint θ)
  have hkey : ∀ θ : E, ∫ x, Real.exp ⟪θ, x⟫ ∂μ = Real.exp (‖θ‖ ^ 2 / (2 * κ)) * F θ := by
    intro θ
    rw [hμeq, integral_withDensity_eq_integral_toReal_smul hdens
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      ← integral_add_right_eq_self _ (κ⁻¹ • θ), hF, ← integral_const_mul]
    congr 1
    funext z
    simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    exact hpt θ z
  have hLC : ConvexOptimization.LogConcaveOn univ F := by
    refine ConvexOptimization.prekopa_marginal_log_concave (n := n) (m := n) f
      hfc.measurable ?_ hfint
    refine ⟨fun _ _ => (Real.exp_pos _).le, fun p _ q _ a b ha hb hab => ?_⟩
    simp only [hf]
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
    have hUi := hUconv.2 (mem_univ (p.2 + κ⁻¹ • p.1)) (mem_univ (q.2 + κ⁻¹ • q.1)) ha hb hab
    have e : a • (p.2 + κ⁻¹ • p.1) + b • (q.2 + κ⁻¹ • q.1) =
        (a • p + b • q).2 + κ⁻¹ • (a • p + b • q).1 := by
      simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst]
      module
    rw [e] at hUi
    have hn := cov_norm_sq_convex_comb p.2 q.2 a b ha hb hab
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hUi hn ⊢
    nlinarith
  have hfun : (fun θ => logLap μ θ - ‖θ‖ ^ 2 / (2 * κ)) = fun θ => Real.log (F θ) := by
    funext θ
    rw [logLap, hkey, Real.log_mul (Real.exp_pos _).ne' (hFpos θ).ne', Real.log_exp]
    ring
  rw [hfun]
  exact cov_logConcaveOn_log_concave hFpos hLC
/-! ## (C4) sub-Gaussian bound for the centred Laplace transform -/

lemma cov_exp_sub_one_sub_le (u : ℝ) : Real.exp u - 1 - u ≤ u ^ 2 * Real.exp |u| := by
  have he : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
  rcases le_or_gt |u| 1 with h | h
  · have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h)).2
    nlinarith [sq_nonneg u]
  · have h1 : Real.exp u ≤ Real.exp |u| := Real.exp_le_exp.mpr (le_abs_self u)
    have h2 : -u ≤ |u| := neg_le_abs u
    have h3 : |u| ≤ u ^ 2 := by
      rw [← sq_abs]; nlinarith
    have h4 : 0 ≤ (u ^ 2 - 1) * (Real.exp |u| - 1) := by
      apply mul_nonneg <;> nlinarith [sq_abs u]
    nlinarith

lemma cov_sq_mul_exp_abs_le (y : ℝ) :
    y ^ 2 * Real.exp |y| ≤ 2 * (Real.exp (2 * y) + Real.exp (-(2 * y))) := by
  have h1 : y ^ 2 ≤ 2 * Real.exp |y| := by
    have := Real.pow_div_factorial_le_exp |y| (abs_nonneg y) 2
    rw [sq_abs] at this
    norm_num [Nat.factorial] at this
    linarith
  have h2 : Real.exp |y| * Real.exp |y| ≤ Real.exp (2 * y) + Real.exp (-(2 * y)) := by
    rw [← Real.exp_add]
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy, show y + y = 2 * y by ring]
      linarith [Real.exp_pos (-(2 * y))]
    · rw [abs_of_neg hy, show -y + -y = -(2 * y) by ring]
      linarith [Real.exp_pos (2 * y)]
  have h3 : 0 ≤ Real.exp |y| := (Real.exp_pos _).le
  nlinarith

lemma slc_integral_inner {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) : ∫ x, ⟪θ, x⟫ ∂μ = ⟪θ, ∫ x, x ∂μ⟫ :=
  integral_inner (slc_integrable_id hμ hκ) θ

lemma slc_integrable_inner {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) : Integrable (fun x => ⟪θ, x⟫) μ :=
  (slc_integrable_id hμ hκ).const_inner θ

lemma slc_integrable_sq_exp {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) :
    Integrable (fun x => ⟪θ, x⟫ ^ 2 * Real.exp |⟪θ, x⟫|) μ := by
  have hI := ((slc_integrable_exp_inner hμ hκ ((2 : ℝ) • θ)).add
    (slc_integrable_exp_inner hμ hκ (-((2 : ℝ) • θ)))).const_mul 2
  refine hI.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := cov_sq_mul_exp_abs_le ⟪θ, x⟫
  simpa [real_inner_smul_left, inner_neg_left] using this

theorem slc_logLap_le {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) :
    logLap μ θ - ‖θ‖ ^ 2 / (2 * κ) ≤ ⟪θ, ∫ x, x ∂μ⟫ := by
  have hprob := hμ.1
  set G : E → ℝ := fun θ => logLap μ θ - ‖θ‖ ^ 2 / (2 * κ) with hG
  have hC : ConcaveOn ℝ univ G := slc_logLaplace_concave hμ hκ
  have hG0 : G 0 = 0 := by simp [hG, logLap]
  set K : ℝ := ∫ x, ⟪θ, x⟫ ^ 2 * Real.exp |⟪θ, x⟫| ∂μ with hK
  have hK0 : 0 ≤ K := integral_nonneg fun x => by positivity
  have hs : ∀ s : ℝ, 0 < s → s ≤ 1 → G θ ≤ ⟪θ, ∫ x, x ∂μ⟫ + s * K := by
    intro s hs0 hs1
    have h1 := hC.2 (mem_univ θ) (mem_univ 0) hs0.le (by linarith : (0 : ℝ) ≤ 1 - s)
      (by ring : s + (1 - s) = 1)
    simp only [smul_zero, add_zero, hG0, smul_eq_mul, mul_zero] at h1
    -- G (s • θ) ≤ M(s) - 1
    have hMint := slc_integrable_exp_inner hμ hκ (s • θ)
    have hMpos : 0 < ∫ x, Real.exp ⟪s • θ, x⟫ ∂μ := integral_exp_pos hMint
    have h2 : G (s • θ) ≤ (∫ x, Real.exp ⟪s • θ, x⟫ ∂μ) - 1 := by
      have := Real.log_le_sub_one_of_pos hMpos
      simp only [hG, logLap]
      have : 0 ≤ ‖s • θ‖ ^ 2 / (2 * κ) := by positivity
      linarith
    have h3 : (∫ x, Real.exp ⟪s • θ, x⟫ ∂μ) - 1 ≤
        s * ⟪θ, ∫ x, x ∂μ⟫ + s ^ 2 * K := by
      rw [← slc_integral_inner hμ hκ, hK, ← integral_const_mul, ← integral_const_mul,
        ← integral_add ((slc_integrable_inner hμ hκ θ).const_mul s)
          ((slc_integrable_sq_exp hμ hκ θ).const_mul _)]
      have h1' : (1 : ℝ) = ∫ x, (1 : ℝ) ∂μ := by simp
      rw [h1', ← integral_sub hMint (integrable_const _)]
      refine integral_mono (hMint.sub (integrable_const _))
        (((slc_integrable_inner hμ hκ θ).const_mul s).add
          ((slc_integrable_sq_exp hμ hκ θ).const_mul _)) fun x => ?_
      have := cov_exp_sub_one_sub_le (s * ⟪θ, x⟫)
      have hle : Real.exp |s * ⟪θ, x⟫| ≤ Real.exp |⟪θ, x⟫| := by
        rw [Real.exp_le_exp, abs_mul, abs_of_pos hs0]
        exact mul_le_of_le_one_left (abs_nonneg _) hs1
      simp only [real_inner_smul_left]
      have : (s * ⟪θ, x⟫) ^ 2 * Real.exp |s * ⟪θ, x⟫| ≤ s ^ 2 * (⟪θ, x⟫ ^ 2 * Real.exp |⟪θ, x⟫|) := by
        rw [mul_pow, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity))
          (by positivity)
      linarith
    have h4 : s * G θ ≤ s * (⟪θ, ∫ x, x ∂μ⟫ + s * K) := by nlinarith
    exact le_of_mul_le_mul_left h4 hs0
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set s := min 1 (ε / (K + 1)) with hsdef
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsK : s * K ≤ ε := by
    have : s ≤ ε / (K + 1) := min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at this
    nlinarith
  linarith [hs s hs0 hs1]

theorem slc_subgaussian {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (θ : E) :
    ∫ x, Real.exp ⟪θ, x - ∫ y, y ∂μ⟫ ∂μ ≤ Real.exp (‖θ‖ ^ 2 / (2 * κ)) := by
  have h := slc_logLap_le hμ hκ θ
  have hI := slc_integrable_exp_inner hμ hκ θ
  have hpos : 0 < ∫ x, Real.exp ⟪θ, x⟫ ∂μ := by have := hμ.1; exact integral_exp_pos hI
  simp only [inner_sub_right, Real.exp_sub]
  rw [integral_div, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  rw [logLap] at h
  rw [← Real.exp_log hpos, Real.exp_le_exp]
  linarith
/-! ## (C5) variance bound and (C6) fourth moment bound -/

lemma cov_pow_le_cosh (y : ℝ) (k : ℕ) : y ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cosh y := by
  refine le_hasSum (Real.hasSum_cosh y) k fun j _ => ?_
  rw [pow_mul]
  positivity

lemma cov_one_add_sq_le_cosh (y : ℝ) : 1 + y ^ 2 / 2 ≤ Real.cosh y := by
  have := sum_le_hasSum (Finset.range 2) (fun j _ => by rw [pow_mul]; positivity)
    (Real.hasSum_cosh y)
  simpa [Finset.sum_range_succ, Nat.factorial] using this

lemma slc_integrable_exp_inner_sub {μ : Measure E} {κ : ℝ}
    (hμ : PhiSobBayes.IsStronglyLogConcave μ κ) (hκ : 0 < κ) (θ m : E) :
    Integrable (fun x => Real.exp ⟪θ, x - m⟫) μ := by
  simp only [inner_sub_right, Real.exp_sub]
  exact (slc_integrable_exp_inner hμ hκ θ).div_const _

lemma slc_integrable_inner_sub_pow {μ : Measure E} {κ : ℝ}
    (hμ : PhiSobBayes.IsStronglyLogConcave μ κ) (hκ : 0 < κ) (v m : E) (k : ℕ) :
    Integrable (fun x => ⟪v, x - m⟫ ^ (2 * k)) μ := by
  have hI := ((slc_integrable_exp_inner_sub hμ hκ v m).add
    (slc_integrable_exp_inner_sub hμ hκ (-v) m)).const_mul ((2 * k).factorial : ℝ)
  refine hI.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [pow_mul]; positivity)]
  have h := cov_pow_le_cosh ⟪v, x - m⟫ k
  have hf : (0 : ℝ) < (2 * k).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf, Real.cosh_eq] at h
  simp only [inner_neg_left, Pi.add_apply]
  nlinarith [Real.exp_pos ⟪v, x - m⟫, Real.exp_pos (-⟪v, x - m⟫)]

/-- `E exp(s Y) + E exp(-s Y) ≤ 2 exp(s² ‖v‖²/(2κ))` for `Y = ⟪v, X - m⟫`. -/
lemma slc_cosh_bound {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (v : E) (s : ℝ) :
    ∫ x, 2 * Real.cosh (s * ⟪v, x - ∫ y, y ∂μ⟫) ∂μ ≤
      2 * Real.exp (s ^ 2 * ‖v‖ ^ 2 / (2 * κ)) := by
  set m := ∫ y, y ∂μ
  have h1 := slc_subgaussian hμ hκ (s • v)
  have h2 := slc_subgaussian hμ hκ (-(s • v))
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1 h2
  simp only [Real.cosh_eq]
  have e : ∀ x, 2 * ((Real.exp (s * ⟪v, x - m⟫) + Real.exp (-(s * ⟪v, x - m⟫))) / 2) =
      Real.exp ⟪s • v, x - m⟫ + Real.exp ⟪-(s • v), x - m⟫ := by
    intro x
    rw [inner_neg_left, real_inner_smul_left]
    ring
  simp_rw [e]
  rw [integral_add (slc_integrable_exp_inner_sub hμ hκ _ _)
    (slc_integrable_exp_inner_sub hμ hκ _ _)]
  linarith

theorem slc_var_le {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (v : E) :
    ∫ x, ⟪v, x - ∫ y, y ∂μ⟫ ^ 2 ∂μ ≤ ‖v‖ ^ 2 / κ := by
  have hprob := hμ.1
  set m := ∫ y, y ∂μ
  set A := ∫ x, ⟪v, x - m⟫ ^ 2 ∂μ
  set c := ‖v‖ ^ 2 / (2 * κ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hA2 : Integrable (fun x => ⟪v, x - m⟫ ^ 2) μ := by
    simpa using slc_integrable_inner_sub_pow hμ hκ v m 1
  have hbound : ∀ s : ℝ, 0 < s → A ≤ 2 * c * Real.exp (s ^ 2 * c) := by
    intro s hs
    have h := slc_cosh_bound hμ hκ v s
    have hlow : ∫ x, (2 + s ^ 2 * ⟪v, x - m⟫ ^ 2) ∂μ ≤
        ∫ x, 2 * Real.cosh (s * ⟪v, x - m⟫) ∂μ := by
      refine integral_mono ((integrable_const _).add (hA2.const_mul _)) ?_ fun x => ?_
      · have hI := (slc_integrable_exp_inner_sub hμ hκ (s • v) m).add
          (slc_integrable_exp_inner_sub hμ hκ (-(s • v)) m)
        refine hI.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Real.cosh_eq, inner_neg_left, real_inner_smul_left, Pi.add_apply]
        ring
      · have := cov_one_add_sq_le_cosh (s * ⟪v, x - m⟫)
        simp only
        nlinarith
    rw [integral_add (integrable_const _) (hA2.const_mul _), integral_const_mul] at hlow
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlow
    have hexp : Real.exp (s ^ 2 * c) - 1 ≤ s ^ 2 * c * Real.exp (s ^ 2 * c) := by
      have := Real.add_one_le_exp (-(s ^ 2 * c))
      have h3 : Real.exp (-(s ^ 2 * c)) * Real.exp (s ^ 2 * c) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (s ^ 2 * c)]
    have e : s ^ 2 * ‖v‖ ^ 2 / (2 * κ) = s ^ 2 * c := by rw [hc]; ring
    rw [e] at h
    have hs2 : 0 < s ^ 2 := by positivity
    have : s ^ 2 * A ≤ s ^ 2 * (2 * c * Real.exp (s ^ 2 * c)) := by nlinarith
    exact le_of_mul_le_mul_left this hs2
  have ht : Filter.Tendsto (fun s : ℝ => 2 * c * Real.exp (s ^ 2 * c)) (nhdsWithin 0 (Ioi 0))
      (nhds (2 * c * Real.exp (0 ^ 2 * c))) :=
    ((by fun_prop : Continuous fun s : ℝ => 2 * c * Real.exp (s ^ 2 * c)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => hbound s hs)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, Real.exp_zero,
    mul_one] at this
  rw [hc] at this
  have e : 2 * (‖v‖ ^ 2 / (2 * κ)) = ‖v‖ ^ 2 / κ := by field_simp
  linarith

lemma slc_fourth_coord {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) (v : E) (hv : ‖v‖ = 1) :
    ∫ x, ⟪v, x - ∫ y, y ∂μ⟫ ^ 4 ∂μ ≤ 18 / κ ^ 2 := by
  set m := ∫ y, y ∂μ
  have hA4 : Integrable (fun x => ⟪v, x - m⟫ ^ 4) μ := by
    simpa using slc_integrable_inner_sub_pow hμ hκ v m 2
  set s := Real.sqrt (2 * κ) with hs
  have hs2 : s ^ 2 = 2 * κ := Real.sq_sqrt (by linarith)
  have h := slc_cosh_bound hμ hκ v s
  rw [hv, hs2] at h
  have e1 : (2 * κ) * 1 ^ 2 / (2 * κ) = 1 := by field_simp
  rw [e1] at h
  have hlow : ∫ x, s ^ 4 / 12 * ⟪v, x - m⟫ ^ 4 ∂μ ≤
      ∫ x, 2 * Real.cosh (s * ⟪v, x - m⟫) ∂μ := by
    refine integral_mono (hA4.const_mul _) ?_ fun x => ?_
    · have hI := (slc_integrable_exp_inner_sub hμ hκ (s • v) m).add
        (slc_integrable_exp_inner_sub hμ hκ (-(s • v)) m)
      refine hI.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Real.cosh_eq, inner_neg_left, real_inner_smul_left, Pi.add_apply]
      ring
    · have := cov_pow_le_cosh (s * ⟪v, x - m⟫) 2
      norm_num [Nat.factorial] at this
      simp only
      rw [mul_pow] at this
      linarith
  rw [integral_const_mul] at hlow
  have hs4 : s ^ 4 = 4 * κ ^ 2 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; ring
  rw [hs4] at hlow
  have he := Real.exp_one_lt_d9
  have hκ2 : 0 < κ ^ 2 := by positivity
  rw [le_div_iff₀ hκ2]
  nlinarith

theorem slc_fourth_moment {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) :
    ∫ x, ‖x - ∫ y, y ∂μ‖ ^ 4 ∂μ ≤ 18 * n ^ 2 / κ ^ 2 := by
  set m := ∫ y, y ∂μ
  set e : Fin n → E := fun i => EuclideanSpace.single i 1
  have he : ∀ i (y : E), ⟪e i, y⟫ = y i := by
    intro i y; simp [e, EuclideanSpace.inner_single_left]
  have hen : ∀ i, ‖e i‖ = 1 := by intro i; simp [e]
  have hpt : ∀ y : E, ‖y‖ ^ 4 ≤ n * ∑ i, ⟪e i, y⟫ ^ 4 := by
    intro y
    have h := EuclideanSpace.real_norm_sq_eq y
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => y i ^ 2)
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    rw [show ‖y‖ ^ 4 = (‖y‖ ^ 2) ^ 2 by ring, h]
    simp only [he]
    have h4 : ∀ i, (y i ^ 2) ^ 2 = y i ^ 4 := fun i => by ring
    simp only [h4] at hcs
    exact hcs
  have hint : ∀ i, Integrable (fun x => ⟪e i, x - m⟫ ^ 4) μ := fun i => by
    simpa using slc_integrable_inner_sub_pow hμ hκ (e i) m 2
  calc ∫ x, ‖x - m‖ ^ 4 ∂μ ≤ ∫ x, (n : ℝ) * ∑ i, ⟪e i, x - m⟫ ^ 4 ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          ((integrable_finsetSum _ fun i _ => hint i).const_mul _)
          (Filter.Eventually.of_forall fun x => hpt (x - m))
    _ = n * ∑ i, ∫ x, ⟪e i, x - m⟫ ^ 4 ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
    _ ≤ n * ∑ _i : Fin n, 18 / κ ^ 2 := by
        gcongr with i
        exact slc_fourth_coord hμ hκ (e i) (hen i)
    _ = 18 * n ^ 2 / κ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end PSBSL

end
end

-- ===== SteinBase.lean =====
section

/-! Base-case estimate for the Stein bound: for a probability measure `P` with covariance
`≤ 1/κ'` and fourth moments `≤ K₄/κ'²`, and `f` with Lipschitz gradient,
`κ' ‖Cov_P(f, X)‖ ≤ E_P ‖∇f‖ + L₂ (2 + 2n + K₄)/√κ'`. -/

set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace PSBSL

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Cauchy–Schwarz for the covariance operator. -/
lemma norm_cov_apply_le (P : Measure E) [IsProbabilityMeasure P] (Y : E → E)
    (hY : AEStronglyMeasurable Y P) (hY2 : Integrable (fun x => ‖Y x‖ ^ 2) P) {κ' : ℝ}
    (hκ' : 0 < κ') (hvar : ∀ v : E, ∫ x, ⟪v, Y x⟫ ^ 2 ∂P ≤ ‖v‖ ^ 2 / κ') (a : E) :
    ‖∫ x, ⟪a, Y x⟫ • Y x ∂P‖ ≤ ‖a‖ / κ' := by
  have hc : ∀ v : E, Continuous (fun y : E => ⟪v, y⟫) := fun v => (innerSL ℝ v).continuous
  have hint : ∀ v : E, Integrable (fun x => ⟪v, Y x⟫ • Y x) P := by
    intro v
    refine Integrable.mono' (hY2.const_mul ‖v‖) ?_ ?_
    · exact ((hc v).comp_aestronglyMeasurable hY).smul hY
    · filter_upwards with x
      rw [norm_smul, Real.norm_eq_abs]
      calc |⟪v, Y x⟫| * ‖Y x‖ ≤ (‖v‖ * ‖Y x‖) * ‖Y x‖ :=
            mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
        _ = ‖v‖ * ‖Y x‖ ^ 2 := by ring
  have hint2 : ∀ v : E, Integrable (fun x => ⟪v, Y x⟫ ^ 2) P := by
    intro v
    refine Integrable.mono' (hY2.const_mul (‖v‖ ^ 2)) ?_ ?_
    · exact (((hc v).comp_aestronglyMeasurable hY)).pow 2
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_pow]
      calc |⟪v, Y x⟫| ^ 2 ≤ (‖v‖ * ‖Y x‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
        _ = ‖v‖ ^ 2 * ‖Y x‖ ^ 2 := by ring
  set w := ∫ x, ⟪a, Y x⟫ • Y x ∂P with hw
  have hww : ‖w‖ ^ 2 = ∫ x, ⟪a, Y x⟫ * ⟪w, Y x⟫ ∂P := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [hw]
    rw [← integral_inner (hint a) w]
    congr 1; funext x
    rw [inner_smul_right, mul_comm]
  -- AM-GM bound for every λ > 0
  have hamgm : ∀ l : ℝ, 0 < l → ‖w‖ ^ 2 ≤ (l * ‖a‖ ^ 2 + ‖w‖ ^ 2 / l) / (2 * κ') := by
    intro l hl
    have hpt : ∀ x, ⟪a, Y x⟫ * ⟪w, Y x⟫ ≤ (l * ⟪a, Y x⟫ ^ 2 + ⟪w, Y x⟫ ^ 2 / l) / 2 := by
      intro x
      have := sq_nonneg (l * ⟪a, Y x⟫ - ⟪w, Y x⟫)
      have h2 : (l * ⟪a, Y x⟫ ^ 2 + ⟪w, Y x⟫ ^ 2 / l) / 2 - ⟪a, Y x⟫ * ⟪w, Y x⟫
          = (l * ⟪a, Y x⟫ - ⟪w, Y x⟫) ^ 2 / (2 * l) := by field_simp; ring
      have h3 : 0 ≤ (l * ⟪a, Y x⟫ - ⟪w, Y x⟫) ^ 2 / (2 * l) := by positivity
      linarith
    have hi1 : Integrable (fun x => ⟪a, Y x⟫ * ⟪w, Y x⟫) P := by
      refine Integrable.mono' (((hint2 a).const_mul (1/2)).add ((hint2 w).const_mul (1/2))) ?_ ?_
      · exact (((hc a).comp_aestronglyMeasurable hY)).mul
          (((hc w).comp_aestronglyMeasurable hY))
      · filter_upwards with x
        rw [Real.norm_eq_abs, abs_mul]
        simp only [Pi.add_apply]
        nlinarith [sq_nonneg (|⟪a, Y x⟫| - |⟪w, Y x⟫|), sq_abs ⟪a, Y x⟫, sq_abs ⟪w, Y x⟫]
    calc ‖w‖ ^ 2 = ∫ x, ⟪a, Y x⟫ * ⟪w, Y x⟫ ∂P := hww
      _ ≤ ∫ x, (l * ⟪a, Y x⟫ ^ 2 + ⟪w, Y x⟫ ^ 2 / l) / 2 ∂P :=
          integral_mono hi1 ((((hint2 a).const_mul l).add ((hint2 w).div_const l)).div_const 2) hpt
      _ = (l * ∫ x, ⟪a, Y x⟫ ^ 2 ∂P + (∫ x, ⟪w, Y x⟫ ^ 2 ∂P) / l) / 2 := by
          rw [integral_div, integral_add ((hint2 a).const_mul l) ((hint2 w).div_const l),
            integral_const_mul, integral_div]
      _ ≤ (l * (‖a‖ ^ 2 / κ') + (‖w‖ ^ 2 / κ') / l) / 2 := by
          gcongr
          · exact hvar a
          · exact hvar w
      _ = (l * ‖a‖ ^ 2 + ‖w‖ ^ 2 / l) / (2 * κ') := by field_simp
  rcases (norm_nonneg w).eq_or_lt with hw0 | hwpos
  · rw [← hw0]; positivity
  rcases (norm_nonneg a).eq_or_lt with ha0 | hapos
  · exfalso
    have := hamgm 1 one_pos
    rw [← ha0] at this
    have h1 : ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 / (2 * κ') := by simpa using this
    -- forces ‖w‖ = 0 when 2κ' > 1; in general use λ → ∞: take λ = 1 / (4κ')... instead use
    -- the bound with arbitrary λ: ‖w‖² ≤ ‖w‖²/(2κ'λ) for all λ
    have h2 := hamgm (1 / κ') (by positivity)
    rw [← ha0] at h2
    have : ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 / 2 := by
      calc ‖w‖ ^ 2 ≤ (1 / κ' * 0 ^ 2 + ‖w‖ ^ 2 / (1 / κ')) / (2 * κ') := h2
        _ = ‖w‖ ^ 2 / 2 := by field_simp; ring
    nlinarith [pow_pos hwpos 2]
  · have := hamgm (‖w‖ / ‖a‖) (div_pos hwpos hapos)
    have h3 : (‖w‖ / ‖a‖ * ‖a‖ ^ 2 + ‖w‖ ^ 2 / (‖w‖ / ‖a‖)) / (2 * κ') = ‖a‖ * ‖w‖ / κ' := by
      field_simp
      ring
    rw [h3] at this
    rw [le_div_iff₀ hκ']
    have : ‖w‖ * ‖w‖ * κ' ≤ ‖a‖ * ‖w‖ := by
      rw [sq, le_div_iff₀ hκ'] at this; linarith
    nlinarith

end PSBSL

namespace PSBSL

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma integrable_norm_sub_pow (P : Measure E) [IsProbabilityMeasure P]
    (hm4 : Integrable (fun x : E => ‖x‖ ^ 4) P) (c : E) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun x : E => ‖x - c‖ ^ k) P := by
  refine Integrable.mono' ((hm4.add (integrable_const 1)).const_mul (2 ^ 4 * (1 + ‖c‖) ^ 4)) ?_ ?_
  · exact ((continuous_id.sub continuous_const).norm.pow k).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖x - c‖ ≤ ‖x‖ + ‖c‖ := norm_sub_le _ _
    have h2 : ‖x - c‖ ^ k ≤ (1 + ‖x‖ + ‖c‖) ^ 4 := by
      calc ‖x - c‖ ^ k ≤ (1 + ‖x‖ + ‖c‖) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
        _ ≤ (1 + ‖x‖ + ‖c‖) ^ 4 := pow_le_pow_right₀ (by linarith [norm_nonneg x, norm_nonneg c]) hk
    have h3 : (1 + ‖x‖ + ‖c‖) ^ 4 ≤ 2 ^ 4 * (1 + ‖c‖) ^ 4 * (‖x‖ ^ 4 + 1) := by
      have hx := norm_nonneg x
      have hc := norm_nonneg c
      rcases le_total ‖x‖ (1 + ‖c‖) with h | h
      · calc (1 + ‖x‖ + ‖c‖) ^ 4 ≤ (2 * (1 + ‖c‖)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
          _ = 2 ^ 4 * (1 + ‖c‖) ^ 4 * 1 := by ring
          _ ≤ 2 ^ 4 * (1 + ‖c‖) ^ 4 * (‖x‖ ^ 4 + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith [pow_nonneg hx 4]
      · calc (1 + ‖x‖ + ‖c‖) ^ 4 ≤ (2 * ‖x‖) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
          _ = 2 ^ 4 * ‖x‖ ^ 4 := by ring
          _ ≤ 2 ^ 4 * (1 + ‖c‖) ^ 4 * (‖x‖ ^ 4 + 1) := by
            have : 1 ≤ (1 + ‖c‖) ^ 4 := one_le_pow₀ (by linarith)
            nlinarith [pow_nonneg hx 4]
    simp only [Pi.add_apply]
    linarith

theorem stein_base (P : Measure E) [IsProbabilityMeasure P] (f : E → ℝ) (hfc : Continuous f)
    (hfb : ∃ B, ∀ x, |f x| ≤ B) (hgc : Continuous (gradient f)) (hgb : ∃ L1, ∀ x, ‖gradient f x‖ ≤ L1)
    {L2 : ℝ} (hL2 : 0 ≤ L2)
    (htaylor : ∀ x y, |f y - f x - ⟪gradient f x, y - x⟫| ≤ L2 / 2 * ‖y - x‖ ^ 2)
    (hglip : ∀ x y, ‖gradient f y - gradient f x‖ ≤ L2 * ‖y - x‖)
    {κ' : ℝ} (hκ' : 0 < κ') {K4 : ℝ}
    (hm4 : Integrable (fun x : E => ‖x‖ ^ 4) P)
    (hvar : ∀ v : E, ∫ x, ⟪v, x - ∫ y, y ∂P⟫ ^ 2 ∂P ≤ ‖v‖ ^ 2 / κ')
    (h2 : ∫ x, ‖x - ∫ y, y ∂P‖ ^ 2 ∂P ≤ n / κ')
    (h4 : ∫ x, ‖x - ∫ y, y ∂P‖ ^ 4 ∂P ≤ K4 / κ' ^ 2) :
    κ' * ‖∫ x, (f x - ∫ y, f y ∂P) • x ∂P‖ ≤
      ∫ x, ‖gradient f x‖ ∂P + L2 * (2 + 2 * n + K4) / Real.sqrt κ' := by
  set m : E := ∫ y, y ∂P with hm
  set Ef : ℝ := ∫ y, f y ∂P with hEf
  obtain ⟨B, hB⟩ := hfb
  obtain ⟨L1, hL1⟩ := hgb
  have hint_id : Integrable (fun x : E => x) P := by
    refine Integrable.mono' ((hm4.add (integrable_const 1))) continuous_id.aestronglyMeasurable ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    rcases le_total ‖x‖ 1 with h | h
    · nlinarith [pow_nonneg (norm_nonneg x) 4]
    · have : ‖x‖ ≤ ‖x‖ ^ 4 := by
        calc ‖x‖ = ‖x‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖x‖ ^ 4 := pow_le_pow_right₀ h (by norm_num)
      linarith
  have hr1 := integrable_norm_sub_pow P hm4 m 1 (by norm_num)
  have hr2 := integrable_norm_sub_pow P hm4 m 2 (by norm_num)
  have hr3 := integrable_norm_sub_pow P hm4 m 3 (by norm_num)
  have hr4 := integrable_norm_sub_pow P hm4 m 4 (by norm_num)
  simp only [pow_one] at hr1
  have hfint : Integrable f P := Integrable.of_bound hfc.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  -- integrability of the vector integrands
  have hsmul_int : ∀ g : E → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C * (1 + ‖x - m‖)) →
      Integrable (fun x => g x • (x - m)) P := by
    intro g hg ⟨C, hC⟩
    refine Integrable.mono' ((hr1.add hr2).const_mul (|C| + |C|)) ?_ ?_
    · exact (hg.smul (continuous_id.sub continuous_const)).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_smul, Real.norm_eq_abs]
      simp only [Pi.add_apply]
      have h1 := hC x
      have hr := norm_nonneg (x - m)
      calc |g x| * ‖x - m‖ ≤ (C * (1 + ‖x - m‖)) * ‖x - m‖ := mul_le_mul_of_nonneg_right h1 hr
        _ ≤ (|C| * (1 + ‖x - m‖)) * ‖x - m‖ := by
          apply mul_le_mul_of_nonneg_right _ hr
          exact mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
        _ ≤ (|C| + |C|) * (‖x - m‖ + ‖x - m‖ ^ 2) := by nlinarith [abs_nonneg C]
  -- Step 1: rewrite the covariance vector
  have hV : ∫ x, (f x - Ef) • x ∂P = ∫ x, (f x - f m) • (x - m) ∂P := by
    have e1 : ∫ x, (f x - Ef) • x ∂P = ∫ x, (f x - Ef) • (x - m) ∂P := by
      have hA : Integrable (fun x => (f x - Ef) • x) P := by
        refine Integrable.mono' (hint_id.norm.const_mul (B + |Ef|)) ?_ ?_
        · exact ((hfc.sub continuous_const).smul continuous_id).aestronglyMeasurable
        · filter_upwards with x
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (by linarith [hB x])) (norm_nonneg _)
      have hBm : Integrable (fun x => (f x - Ef) • m) P := (hfint.sub (integrable_const _)).smul_const m
      have : (fun x => (f x - Ef) • (x - m)) = fun x => (f x - Ef) • x - (f x - Ef) • m := by
        funext x; rw [smul_sub]
      rw [this, integral_sub hA hBm, integral_smul_const, integral_sub hfint (integrable_const _)]
      simp [hEf]
    have e2 : ∫ x, (f x - Ef) • (x - m) ∂P = ∫ x, (f x - f m) • (x - m) ∂P := by
      have hC1 : Integrable (fun x => (f x - f m) • (x - m)) P := hsmul_int _ (hfc.sub continuous_const)
        ⟨2 * B, fun x => by
          calc |f x - f m| ≤ |f x| + |f m| := abs_sub _ _
            _ ≤ 2 * B := by linarith [hB x, hB m]
            _ ≤ 2 * B * (1 + ‖x - m‖) := by
              have : 0 ≤ B := (abs_nonneg _).trans (hB x)
              nlinarith [norm_nonneg (x - m)]⟩
      have hC2 : Integrable (fun x => (f m - Ef) • (x - m)) P :=
        Integrable.smul (f m - Ef) (hint_id.sub (integrable_const m))
      have : (fun x => (f x - Ef) • (x - m)) = fun x => (f x - f m) • (x - m) + (f m - Ef) • (x - m) := by
        funext x; rw [← add_smul]; ring_nf
      rw [this, integral_add hC1 hC2, integral_smul, integral_sub hint_id (integrable_const m)]
      simp [hm]
    rw [e1, e2]
  -- Step 2: split with the Taylor remainder
  set a := gradient f m with ha
  set R : E → ℝ := fun x => f x - f m - ⟪a, x - m⟫ with hR
  have hRb : ∀ x, |R x| ≤ L2 / 2 * ‖x - m‖ ^ 2 := fun x => htaylor m x
  have hI1 : Integrable (fun x => ⟪a, x - m⟫ • (x - m)) P :=
    hsmul_int _ ((innerSL ℝ a).continuous.comp (continuous_id.sub continuous_const))
      ⟨‖a‖, fun x => by
        calc |⟪a, x - m⟫| ≤ ‖a‖ * ‖x - m‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖a‖ * (1 + ‖x - m‖) := by nlinarith [norm_nonneg a]⟩
  have hI2 : Integrable (fun x => R x • (x - m)) P := by
    refine Integrable.mono' (hr3.const_mul (L2 / 2)) ?_ ?_
    · exact (((hfc.sub continuous_const).sub ((innerSL ℝ a).continuous.comp
        (continuous_id.sub continuous_const))).smul (continuous_id.sub continuous_const)).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_smul, Real.norm_eq_abs]
      calc |R x| * ‖x - m‖ ≤ (L2 / 2 * ‖x - m‖ ^ 2) * ‖x - m‖ :=
            mul_le_mul_of_nonneg_right (hRb x) (norm_nonneg _)
        _ = L2 / 2 * ‖x - m‖ ^ 3 := by ring
  have hsplit : ∫ x, (f x - f m) • (x - m) ∂P =
      ∫ x, ⟪a, x - m⟫ • (x - m) ∂P + ∫ x, R x • (x - m) ∂P := by
    rw [← integral_add hI1 hI2]
    congr 1; funext x
    rw [← add_smul]; simp [hR]
  -- bounds
  have hb1 : ‖∫ x, ⟪a, x - m⟫ • (x - m) ∂P‖ ≤ ‖a‖ / κ' :=
    norm_cov_apply_le P (fun x => x - m) (continuous_id.sub continuous_const).aestronglyMeasurable
      hr2 hκ' hvar a
  have hb2 : ‖∫ x, R x • (x - m) ∂P‖ ≤ L2 / 2 * ∫ x, ‖x - m‖ ^ 3 ∂P := by
    calc ‖∫ x, R x • (x - m) ∂P‖ ≤ ∫ x, ‖R x • (x - m)‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ x, L2 / 2 * ‖x - m‖ ^ 3 ∂P := by
          apply integral_mono hI2.norm (hr3.const_mul _)
          intro x
          simp only
          rw [norm_smul, Real.norm_eq_abs]
          calc |R x| * ‖x - m‖ ≤ (L2 / 2 * ‖x - m‖ ^ 2) * ‖x - m‖ :=
                mul_le_mul_of_nonneg_right (hRb x) (norm_nonneg _)
            _ = L2 / 2 * ‖x - m‖ ^ 3 := by ring
      _ = L2 / 2 * ∫ x, ‖x - m‖ ^ 3 ∂P := integral_const_mul _ _
  have hgint : Integrable (fun x => ‖gradient f x‖) P :=
    Integrable.of_bound hgc.norm.aestronglyMeasurable L1
      (Filter.Eventually.of_forall fun x => by rw [norm_norm]; exact hL1 x)
  have hb3 : ‖a‖ ≤ ∫ x, ‖gradient f x‖ ∂P + L2 * ∫ x, ‖x - m‖ ∂P := by
    have hpt : ∀ x, ‖a‖ ≤ ‖gradient f x‖ + L2 * ‖x - m‖ := by
      intro x
      have := hglip m x
      calc ‖a‖ = ‖gradient f x - (gradient f x - gradient f m)‖ := by rw [ha]; congr 1; abel
        _ ≤ ‖gradient f x‖ + ‖gradient f x - gradient f m‖ := norm_sub_le _ _
        _ ≤ ‖gradient f x‖ + L2 * ‖x - m‖ := by linarith
    calc ‖a‖ = ∫ _x, ‖a‖ ∂P := by simp
      _ ≤ ∫ x, (‖gradient f x‖ + L2 * ‖x - m‖) ∂P :=
          integral_mono (integrable_const _) (hgint.add (hr1.const_mul L2)) hpt
      _ = ∫ x, ‖gradient f x‖ ∂P + L2 * ∫ x, ‖x - m‖ ∂P := by
          rw [integral_add hgint (hr1.const_mul L2), integral_const_mul]
  -- moment bounds via AM-GM
  set δ := Real.sqrt κ' with hδ
  have hδpos : 0 < δ := Real.sqrt_pos.2 hκ'
  have hδsq : δ ^ 2 = κ' := Real.sq_sqrt hκ'.le
  have hm1 : ∫ x, ‖x - m‖ ∂P ≤ (1 + n) / (2 * δ) := by
    have hpt : ∀ x, ‖x - m‖ ≤ (1 / δ + δ * ‖x - m‖ ^ 2) / 2 := by
      intro x
      have h := sq_nonneg (δ * ‖x - m‖ - 1)
      have : (1 / δ + δ * ‖x - m‖ ^ 2) / 2 - ‖x - m‖ = (δ * ‖x - m‖ - 1) ^ 2 / (2 * δ) := by
        field_simp; ring
      have : 0 ≤ (δ * ‖x - m‖ - 1) ^ 2 / (2 * δ) := by positivity
      linarith
    calc ∫ x, ‖x - m‖ ∂P ≤ ∫ x, (1 / δ + δ * ‖x - m‖ ^ 2) / 2 ∂P :=
          integral_mono hr1 (((integrable_const _).add (hr2.const_mul δ)).div_const 2) hpt
      _ = (1 / δ + δ * ∫ x, ‖x - m‖ ^ 2 ∂P) / 2 := by
          rw [integral_div, integral_add (integrable_const _) (hr2.const_mul δ), integral_const_mul]
          simp
      _ ≤ (1 / δ + δ * (n / κ')) / 2 := by gcongr
      _ = (1 + n) / (2 * δ) := by rw [← hδsq]; field_simp
  have hm3 : ∫ x, ‖x - m‖ ^ 3 ∂P ≤ (n + K4) / (2 * κ' * δ) := by
    have hpt : ∀ x, ‖x - m‖ ^ 3 ≤ (‖x - m‖ ^ 2 / δ + δ * ‖x - m‖ ^ 4) / 2 := by
      intro x
      have h := sq_nonneg (‖x - m‖ - δ * ‖x - m‖ ^ 2)
      have : (‖x - m‖ ^ 2 / δ + δ * ‖x - m‖ ^ 4) / 2 - ‖x - m‖ ^ 3 =
          (‖x - m‖ - δ * ‖x - m‖ ^ 2) ^ 2 / (2 * δ) := by field_simp; ring
      have : 0 ≤ (‖x - m‖ - δ * ‖x - m‖ ^ 2) ^ 2 / (2 * δ) := by positivity
      linarith
    calc ∫ x, ‖x - m‖ ^ 3 ∂P ≤ ∫ x, (‖x - m‖ ^ 2 / δ + δ * ‖x - m‖ ^ 4) / 2 ∂P :=
          integral_mono hr3 (((hr2.div_const δ).add (hr4.const_mul δ)).div_const 2) hpt
      _ = ((∫ x, ‖x - m‖ ^ 2 ∂P) / δ + δ * ∫ x, ‖x - m‖ ^ 4 ∂P) / 2 := by
          rw [integral_div, integral_add (hr2.div_const δ) (hr4.const_mul δ), integral_const_mul,
            integral_div]
      _ ≤ ((n / κ') / δ + δ * (K4 / κ' ^ 2)) / 2 := by gcongr
      _ = (n + K4) / (2 * κ' * δ) := by rw [← hδsq]; field_simp
  -- assemble
  rw [hV, hsplit]
  have hK4 : 0 ≤ K4 := by
    have : 0 ≤ ∫ x, ‖x - m‖ ^ 4 ∂P := integral_nonneg fun x => by positivity
    have := this.trans h4
    rwa [le_div_iff₀ (by positivity), zero_mul] at this
  calc κ' * ‖∫ x, ⟪a, x - m⟫ • (x - m) ∂P + ∫ x, R x • (x - m) ∂P‖
      ≤ κ' * (‖a‖ / κ' + L2 / 2 * ∫ x, ‖x - m‖ ^ 3 ∂P) := by
        apply mul_le_mul_of_nonneg_left _ hκ'.le
        exact (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ = ‖a‖ + κ' * (L2 / 2) * ∫ x, ‖x - m‖ ^ 3 ∂P := by field_simp
    _ ≤ (∫ x, ‖gradient f x‖ ∂P + L2 * ((1 + n) / (2 * δ))) +
          κ' * (L2 / 2) * ((n + K4) / (2 * κ' * δ)) := by
        gcongr
        exact hb3.trans (by gcongr)
    _ ≤ ∫ x, ‖gradient f x‖ ∂P + L2 * (2 + 2 * n + K4) / δ := by
        have e : κ' * (L2 / 2) * ((n + K4) / (2 * κ' * δ)) = L2 * (n + K4) / (4 * δ) := by
          field_simp; ring
        rw [e]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have : L2 * ((1 + n) / (2 * δ)) + L2 * (n + K4) / (4 * δ) ≤ L2 * (2 + 2 * n + K4) / δ := by
          have e2 : L2 * ((1 + n) / (2 * δ)) + L2 * (n + K4) / (4 * δ)
              = L2 * (2 + 3 * n + K4) / (4 * δ) := by field_simp; ring
          rw [e2, div_le_div_iff₀ (by positivity) hδpos]
          have : 0 ≤ L2 * δ := by positivity
          nlinarith [mul_nonneg this hn, mul_nonneg this hK4]
        linarith

end PSBSL

end
end

-- ===== TestFn.lean =====
section

/-! Second-order regularity of test functions: Lipschitz gradient and Taylor bound. -/

set_option autoImplicit false

open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace PSBSL

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma tc_fderiv_eq {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ fderiv ℝ f = fderiv ℝ g ∧
      ContDiff ℝ ∞ f := by
  obtain ⟨⟨c, g, hg, hgc, rfl⟩, -⟩ := hf
  refine ⟨g, hg, hgc, ?_, contDiff_const.add hg⟩
  funext x; exact fderiv_const_add (𝕜 := ℝ) (f := g) c

lemma tc_partial_lipschitz {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) (i : Fin n) :
    ∃ C : NNReal, LipschitzWith C (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  obtain ⟨g, hg, hgc, hfg, -⟩ := tc_fderiv_eq hf
  rw [hfg]
  have h1 : ContDiff ℝ ∞ (fun x => fderiv ℝ g x (EuclideanSpace.single i 1)) :=
    (hg.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have h1' : HasCompactSupport (fun x => fderiv ℝ g x (EuclideanSpace.single i 1)) := by
    apply (hgc.fderiv (𝕜 := ℝ)).mono
    intro x hx h0; apply hx; simp [h0]
  exact h1.lipschitzWith_of_hasCompactSupport h1' (by simp)

lemma gradient_apply_eq (f : E → ℝ) (x : E) (i : Fin n) :
    (gradient f x) i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have h1 : ⟪gradient f x, EuclideanSpace.single i (1:ℝ)⟫ = fderiv ℝ f x (EuclideanSpace.single i 1) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← h1, EuclideanSpace.inner_single_right]; simp

lemma tc_gradient_lipschitz {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : E, ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖ := by
  choose C hC using fun i => tc_partial_lipschitz hf i
  refine ⟨∑ i, (C i : ℝ), Finset.sum_nonneg (fun i _ => (C i).2), fun x y => ?_⟩
  have hcoord : ∀ i, |(gradient f y - gradient f x) i| ≤ (C i : ℝ) * ‖y - x‖ := by
    intro i
    have := (hC i).dist_le_mul y x
    rw [Real.dist_eq, dist_eq_norm] at this
    simpa [gradient_apply_eq] using this
  have hsq : ‖gradient f y - gradient f x‖ ^ 2 ≤ ((∑ i, (C i : ℝ)) * ‖y - x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(gradient f y - gradient f x) i‖ ^ 2 ≤ ∑ i, ((C i : ℝ) * ‖y - x‖) ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
      _ = (∑ i, (C i : ℝ) ^ 2) * ‖y - x‖ ^ 2 := by rw [Finset.sum_mul]; congr 1; funext i; ring
      _ ≤ (∑ i, (C i : ℝ)) ^ 2 * ‖y - x‖ ^ 2 := by
          gcongr
          exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => (C i).2)
      _ = ((∑ i, (C i : ℝ)) * ‖y - x‖) ^ 2 := by ring
  have h0 : 0 ≤ (∑ i, (C i : ℝ)) * ‖y - x‖ :=
    mul_nonneg (Finset.sum_nonneg (fun i _ => (C i).2)) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 (by norm_num)).1 hsq

lemma tc_fderiv_lipschitz {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : E, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖ := by
  obtain ⟨L, hL0, hL⟩ := tc_gradient_lipschitz hf
  refine ⟨L, hL0, fun x y => ?_⟩
  have : fderiv ℝ f y - fderiv ℝ f x =
      (InnerProductSpace.toDual ℝ E) (gradient f y - gradient f x) := by
    simp [gradient, map_sub]
  rw [this, LinearIsometryEquiv.norm_map]
  exact hL x y

lemma tc_taylor {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : E,
      |f y - f x - ⟪gradient f x, y - x⟫| ≤ L * ‖y - x‖ ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := tc_fderiv_lipschitz hf
  obtain ⟨-, -, -, -, hfs⟩ := tc_fderiv_eq hf
  refine ⟨L, hL0, fun x y => ?_⟩
  have hdiff : Differentiable ℝ f := hfs.differentiable (by simp)
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := f) (s := segment ℝ x y)
    (φ := fderiv ℝ f x) (C := L * ‖y - x‖) (fun z _ => hdiff z)
    (fun z hz => by
      have hzx : ‖z - x‖ ≤ ‖y - x‖ := by
        obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
        have : a • x + b • y - x = b • (y - x) := by
          have ha' : a = 1 - b := by linarith
          rw [ha', smul_sub, sub_smul, one_smul]; abel
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
        have : b ≤ 1 := by linarith
        nlinarith [norm_nonneg (y - x)]
      calc ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ L * ‖z - x‖ := hL x z
        _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left hzx hL0)
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hg : ⟪gradient f x, y - x⟫ = fderiv ℝ f x (y - x) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [hg, ← Real.norm_eq_abs]
  calc ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ L * ‖y - x‖ * ‖y - x‖ := key
    _ = L * ‖y - x‖ ^ 2 := by ring

lemma tc_gradient_bounded {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ L1 : ℝ, ∀ x, ‖gradient f x‖ ≤ L1 := by
  obtain ⟨g, hg, hgc, hfg, -⟩ := tc_fderiv_eq hf
  have h3 : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  obtain ⟨L, hL⟩ := h3.bounded_above_of_compact_support (hgc.fderiv (𝕜 := ℝ))
  refine ⟨L, fun x => ?_⟩
  have : gradient f x = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) := rfl
  rw [this, LinearIsometryEquiv.norm_map, hfg]
  exact hL x

end PSBSL

end
end

-- ===== SteinSLC.lean =====
section

/-! Base-case Stein estimate for strongly log-concave measures and test functions. -/

set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace PSBSL

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma norm_sq_eq_sum_inner_single (y : E) :
    ‖y‖ ^ 2 = ∑ i : Fin n, ⟪EuclideanSpace.single i (1:ℝ), y⟫ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  congr 1; funext i
  rw [EuclideanSpace.inner_single_left]; simp

theorem slc_second_moment {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) : ∫ x, ‖x - ∫ y, y ∂μ‖ ^ 2 ∂μ ≤ n / κ := by
  have hprob := hμ.1
  set m := ∫ y, y ∂μ
  have hint : ∀ i : Fin n, Integrable (fun x => ⟪EuclideanSpace.single i (1:ℝ), x - m⟫ ^ 2) μ := by
    intro i
    have h2 := slc_integrable_pow hμ hκ 2
    refine Integrable.mono' ((h2.add (integrable_const 1)).const_mul (2 * (1 + ‖m‖) ^ 2)) ?_ ?_
    · exact (((innerSL ℝ _).continuous.comp (continuous_id.sub continuous_const)).pow 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      have h1 : ⟪EuclideanSpace.single i (1:ℝ), x - m⟫ ^ 2 ≤ ‖x - m‖ ^ 2 := by
        have := abs_real_inner_le_norm (EuclideanSpace.single i (1:ℝ)) (x - m)
        rw [EuclideanSpace.norm_single, norm_one, one_mul] at this
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      have h3 : ‖x - m‖ ^ 2 ≤ 2 * (1 + ‖m‖) ^ 2 * (‖x‖ ^ 2 + 1) := by
        have := norm_sub_le x m
        have hx := norm_nonneg x
        have hm := norm_nonneg m
        have h4 : ‖x - m‖ ^ 2 ≤ (‖x‖ + ‖m‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        nlinarith [sq_nonneg (‖x‖ - ‖m‖), sq_nonneg (‖x‖ * ‖m‖), mul_nonneg hx hm,
          mul_nonneg (mul_nonneg hx hm) hm, sq_nonneg ‖x‖, sq_nonneg ‖m‖]
      linarith
  calc ∫ x, ‖x - m‖ ^ 2 ∂μ = ∫ x, ∑ i : Fin n, ⟪EuclideanSpace.single i (1:ℝ), x - m⟫ ^ 2 ∂μ := by
        congr 1; funext x; exact norm_sq_eq_sum_inner_single _
    _ = ∑ i : Fin n, ∫ x, ⟪EuclideanSpace.single i (1:ℝ), x - m⟫ ^ 2 ∂μ :=
        integral_finsetSum _ (fun i _ => hint i)
    _ ≤ ∑ _i : Fin n, 1 / κ := by
        apply Finset.sum_le_sum; intro i _
        have := slc_var_le hμ hκ (EuclideanSpace.single i (1:ℝ))
        rwa [EuclideanSpace.norm_single, norm_one, one_pow] at this
    _ = n / κ := by simp [div_eq_mul_inv]

/-- Stein base estimate for a strongly log-concave measure. -/
theorem slc_stein_base {μ : Measure E} {κ : ℝ} (hμ : PhiSobBayes.IsStronglyLogConcave μ κ)
    (hκ : 0 < κ) {J : Set ℝ} (f : E → ℝ) (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ L : ℝ, 0 ≤ L ∧ κ * ‖∫ x, (f x - ∫ y, f y ∂μ) • x ∂μ‖ ≤
      ∫ x, ‖gradient f x‖ ∂μ + L * (2 + 2 * n + 18 * n ^ 2) / Real.sqrt κ := by
  have hprob := hμ.1
  obtain ⟨La, hLa0, hLa⟩ := tc_gradient_lipschitz hf
  obtain ⟨Lb, hLb0, hLb⟩ := tc_taylor hf
  set L := La + 2 * Lb
  have hfc : Continuous f := (tc_fderiv_eq hf).choose_spec.2.2.2.continuous
  have hfb : ∃ B, ∀ x, |f x| ≤ B := by
    obtain ⟨⟨c, g, hg, hgc, rfl⟩, -⟩ := hf
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    exact ⟨|c| + C, fun x => by
      have := hC x; rw [Real.norm_eq_abs] at this
      calc |c + g x| ≤ |c| + |g x| := abs_add_le _ _
        _ ≤ |c| + C := by linarith⟩
  have hgc : Continuous (gradient f) := by
    have h := (tc_fderiv_eq hf).choose_spec.2.2.2
    have : gradient f = fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) := rfl
    rw [this]; exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp (h.continuous_fderiv (by simp))
  refine ⟨L, by positivity, ?_⟩
  have := stein_base μ f hfc hfb hgc (tc_gradient_bounded hf) (L2 := L) (by positivity)
    (fun x y => (hLb x y).trans (by
      have : Lb ≤ L / 2 := by simp only [L]; linarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)))
    (fun x y => (hLa x y).trans (by
      have : La ≤ L := by simp only [L]; linarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)))
    hκ (K4 := 18 * n ^ 2) (slc_integrable_pow hμ hκ 4) (slc_var_le hμ hκ)
    (slc_second_moment hμ hκ) (slc_fourth_moment hμ hκ)
  exact this

end PSBSL

end
end

-- ===== Gronwall.lean =====
section

/-! A backward Grönwall inequality with kernel `1/(κ+s)`:
if `u t ≤ A + ∫_t^T u s / (κ+s) ds` on `[t₀,T]` (with `κ + t₀ > 0`, `u` bounded) then
`(κ+t) u t ≤ (κ+T) A`. -/

set_option autoImplicit false

open MeasureTheory intervalIntegral

noncomputable section

namespace PSBSL

lemma integral_inv_sq_shift {κ t T : ℝ} (ht : 0 < κ + t) (htT : t ≤ T) :
    ∫ s in t..T, 1 / (κ + s) ^ 2 = 1 / (κ + t) - 1 / (κ + T) := by
  have hderiv : ∀ s ∈ Set.uIcc t T, HasDerivAt (fun s => -(1 / (κ + s))) (1 / (κ + s) ^ 2) s := by
    intro s hs
    rw [Set.uIcc_of_le htT] at hs
    have hpos : 0 < κ + s := by linarith [hs.1]
    have h1 : HasDerivAt (fun s => κ + s) 1 s := (hasDerivAt_id s).const_add κ
    have h2 : HasDerivAt (fun s => (κ + s)⁻¹) (-1 / (κ + s) ^ 2) s := h1.inv hpos.ne'
    have h3 : HasDerivAt (fun s => -(κ + s)⁻¹) (-(-1 / (κ + s) ^ 2)) s := h2.neg
    have e1 : (fun s => -(1 / (κ + s))) = (fun s => -(κ + s)⁻¹) := by
      funext s; rw [one_div]
    rw [e1]
    convert h3 using 1
    ring
  have hcont : ContinuousOn (fun s => 1 / (κ + s) ^ 2) (Set.uIcc t T) := by
    intro s hs
    rw [Set.uIcc_of_le htT] at hs
    have hpos : 0 < κ + s := by linarith [hs.1]
    exact (continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2)
      (pow_ne_zero 2 hpos.ne')).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  ring

/-- backward Grönwall with kernel `1/(κ+s)` -/
theorem gronwall_inv {κ t₀ T A : ℝ} (hκ : 0 < κ + t₀) (hT : t₀ ≤ T) (u : ℝ → ℝ)
    (hbdd : ∃ M, ∀ s ∈ Set.Icc t₀ T, u s ≤ M)
    (hint : IntervalIntegrable (fun s => u s / (κ + s)) volume t₀ T)
    (hu : ∀ t ∈ Set.Icc t₀ T, u t ≤ A + ∫ s in t..T, u s / (κ + s)) :
    ∀ t ∈ Set.Icc t₀ T, (κ + t) * u t ≤ (κ + T) * A := by
  obtain ⟨M, hM⟩ := hbdd
  set S : Set ℝ := (fun s => (κ + s) * u s - (κ + T) * A) '' Set.Icc t₀ T with hS
  have hSne : S.Nonempty := ⟨_, ⟨t₀, ⟨le_rfl, hT⟩, rfl⟩⟩
  have hSbdd : BddAbove S := by
    refine ⟨(κ + T) * |M| + |(κ + T) * A|, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hks : 0 < κ + s := by linarith [hs.1]
    have hkT : κ + s ≤ κ + T := by linarith [hs.2]
    have : (κ + s) * u s ≤ (κ + T) * |M| := by
      calc (κ + s) * u s ≤ (κ + s) * |M| :=
            mul_le_mul_of_nonneg_left ((hM s hs).trans (le_abs_self M)) hks.le
        _ ≤ (κ + T) * |M| := mul_le_mul_of_nonneg_right hkT (abs_nonneg M)
    linarith [neg_abs_le ((κ + T) * A)]
  set B := sSup S with hB
  have hle : ∀ s ∈ Set.Icc t₀ T, (κ + s) * u s - (κ + T) * A ≤ B :=
    fun s hs => le_csSup hSbdd ⟨s, hs, rfl⟩
  -- key estimate
  have hkey : ∀ t ∈ Set.Icc t₀ T,
      (κ + t) * u t - (κ + T) * A ≤ B * ((T - t₀) / (κ + T)) ∨ B ≤ 0 := by
    intro t ht
    by_cases hB0 : B ≤ 0
    · exact Or.inr hB0
    left
    push Not at hB0
    have hkt : 0 < κ + t := by linarith [ht.1]
    have hkT : 0 < κ + T := by linarith [ht.2]
    have hus : ∀ s ∈ Set.Icc t T, u s / (κ + s) ≤ ((κ + T) * A + B) * (1 / (κ + s) ^ 2) := by
      intro s hs
      have hs' : s ∈ Set.Icc t₀ T := ⟨ht.1.trans hs.1, hs.2⟩
      have hks : 0 < κ + s := by linarith [hs.1]
      have := hle s hs'
      rw [div_le_iff₀ hks]
      have : u s ≤ ((κ + T) * A + B) / (κ + s) := by
        rw [le_div_iff₀ hks]; linarith
      calc u s ≤ ((κ + T) * A + B) / (κ + s) := this
        _ = ((κ + T) * A + B) * (1 / (κ + s) ^ 2) * (κ + s) := by field_simp
    have hint' : IntervalIntegrable (fun s => u s / (κ + s)) volume t T :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hT, Set.uIcc_of_le ht.2]
        exact Set.Icc_subset_Icc ht.1 le_rfl)
    have hcont2 : IntervalIntegrable (fun s => ((κ + T) * A + B) * (1 / (κ + s) ^ 2)) volume t T := by
      apply ContinuousOn.intervalIntegrable
      intro s hs
      rw [Set.uIcc_of_le ht.2] at hs
      have hks : 0 < κ + s := by linarith [hs.1]
      exact (continuousAt_const.mul (continuousAt_const.div
        ((continuousAt_const.add continuousAt_id).pow 2) (pow_ne_zero 2 hks.ne'))).continuousWithinAt
    have hI : ∫ s in t..T, u s / (κ + s) ≤ ((κ + T) * A + B) * (1 / (κ + t) - 1 / (κ + T)) := by
      calc ∫ s in t..T, u s / (κ + s) ≤ ∫ s in t..T, ((κ + T) * A + B) * (1 / (κ + s) ^ 2) :=
            integral_mono_on ht.2 hint' hcont2 hus
        _ = ((κ + T) * A + B) * (1 / (κ + t) - 1 / (κ + T)) := by
            rw [intervalIntegral.integral_const_mul, integral_inv_sq_shift hkt ht.2]
    have h1 := hu t ht
    have h2 : (κ + t) * u t ≤ (κ + t) * (A + ((κ + T) * A + B) * (1 / (κ + t) - 1 / (κ + T))) :=
      mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hkt.le
    have h3 : (κ + t) * (A + ((κ + T) * A + B) * (1 / (κ + t) - 1 / (κ + T))) - (κ + T) * A
        = B * ((T - t) / (κ + T)) := by
      field_simp; ring
    have h4 : B * ((T - t) / (κ + T)) ≤ B * ((T - t₀) / (κ + T)) := by
      apply mul_le_mul_of_nonneg_left _ hB0.le
      apply div_le_div_of_nonneg_right _ hkT.le
      linarith [ht.1]
    linarith
  -- conclude B ≤ 0
  have hBle : B ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hkT : 0 < κ + T := by linarith
    have hρ : (T - t₀) / (κ + T) < 1 := by rw [div_lt_one hkT]; linarith
    have : B ≤ B * ((T - t₀) / (κ + T)) := by
      apply csSup_le hSne
      rintro _ ⟨s, hs, rfl⟩
      rcases hkey s hs with h | h
      · exact h
      · linarith
    nlinarith
  intro t ht
  linarith [hle t ht]

end PSBSL

end
end

-- ===== BE.lean =====
section

/-! Bakry–Émery for strongly log-concave measures, assuming the posterior Stein bound. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

noncomputable section

namespace PSBSL

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma be_tc_range {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ lo hi : ℝ, lo ∈ J ∧ hi ∈ J ∧ ∀ x, f x ∈ Set.Icc lo hi := by
  have hJf := hf.2
  obtain ⟨⟨c, g, hg, hgc, hfe⟩, -⟩ := hf
  have hcpt : IsCompact (Set.range f) := by
    have : Set.range f = (fun u => c + u) '' Set.range g := by
      rw [hfe, ← Set.range_comp]; rfl
    rw [this]
    exact (hgc.isCompact_range hg.continuous).image (by fun_prop)
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  obtain ⟨lo, ⟨x0, rfl⟩, hlo⟩ := hcpt.exists_isLeast hne
  obtain ⟨hi, ⟨x1, rfl⟩, hhi⟩ := hcpt.exists_isGreatest hne
  exact ⟨f x0, f x1, hJf x0, hJf x1, fun x => ⟨hlo ⟨x, rfl⟩, hhi ⟨x, rfl⟩⟩⟩

lemma be_tc_lipschitz {J : Set ℝ} {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J) :
    ∃ L : NNReal, LipschitzWith L f := by
  obtain ⟨⟨c, g, hg, hgc, rfl⟩, -⟩ := hf
  obtain ⟨L, hL⟩ := hg.lipschitzWith_of_hasCompactSupport hgc (by simp)
  refine ⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [Real.dist_eq, add_sub_add_left_eq_sub]
  rw [← Real.dist_eq]; exact hL.dist_le_mul x y

lemma be_measurable_pcov (π : Measure E) [SFinite π] {f : E → ℝ} (hf : Measurable f) {s : ℝ}
    (hs : 0 < s) : Measurable (fun θ => pcov π s θ f) := by
  have h := (eng_measurable_pcov π hf).comp
    ((measurable_const (a := s)).prodMk (measurable_const_smul ((Real.sqrt s)⁻¹) : Measurable (fun θ : E => (Real.sqrt s)⁻¹ • θ)))
  convert h using 1
  funext θ
  simp only [Function.comp_apply]
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hs).ne', one_smul]

lemma be_adm_d2 {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) : ContinuousOn (deriv (deriv Φ)) J := by
  have hd1 : ContDiffOn ℝ ∞ (deriv Φ) J := hΦ.1.deriv_of_isOpen hJ.1 (by simp)
  have hd2 : ContDiffOn ℝ ∞ (deriv (deriv Φ)) J := hd1.deriv_of_isOpen hJ.1 (by simp)
  exact hd2.continuousOn

/-- measurability of `F ∘ h` for `F` continuous on `[lo,hi]` and `h` valued there -/
lemma be_meas_comp {α : Type*} [MeasurableSpace α] {F : ℝ → ℝ} {lo hi : ℝ} (hle : lo ≤ hi)
    (hF : ContinuousOn F (Set.Icc lo hi)) {h : α → ℝ} (hh : Measurable h)
    (hr : ∀ a, h a ∈ Set.Icc lo hi) : Measurable (fun a => F (h a)) := by
  have hc : Continuous (fun z => F (Set.projIcc lo hi hle z)) :=
    hF.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun z => (Set.projIcc lo hi hle z).2)
  have : (fun a => F (h a)) = (fun z => F (Set.projIcc lo hi hle z)) ∘ h := by
    funext a; simp [Set.projIcc_of_mem hle (hr a)]
  rw [this]; exact hc.measurable.comp hh

lemma be_bdd_comp {F : ℝ → ℝ} {lo hi : ℝ} (hF : ContinuousOn F (Set.Icc lo hi)) :
    ∃ M, ∀ z ∈ Set.Icc lo hi, |F z| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hF).isBounded.exists_norm_le
  exact ⟨M, fun z hz => by simpa [Real.norm_eq_abs] using hM _ ⟨z, hz, rfl⟩⟩

lemma be_pmean_mem {π : Measure E} [IsProbabilityMeasure π] {t : ℝ} (ht : 0 < t) (θ : E)
    {f : E → ℝ} (hfm : Measurable f) {lo hi : ℝ} (hfr : ∀ x, f x ∈ Set.Icc lo hi) :
    pmean π t θ f ∈ Set.Icc lo hi := by
  have := post_isProb (π := π) ht θ
  have hint : Integrable f (post π t θ) := Integrable.of_bound hfm.aestronglyMeasurable
    (max |lo| |hi|) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [neg_abs_le lo, le_max_left |lo| |hi|, (hfr x).1]
      · linarith [le_abs_self hi, le_max_right |lo| |hi|, (hfr x).2])
  constructor
  · calc lo = ∫ _x, lo ∂(post π t θ) := by simp
      _ ≤ pmean π t θ f := integral_mono (integrable_const _) hint (fun x => (hfr x).1)
  · calc pmean π t θ f ≤ ∫ _x, hi ∂(post π t θ) := integral_mono hint (integrable_const _) (fun x => (hfr x).2)
      _ = hi := by simp

/-- Bakry–Émery, conditional on the posterior Stein bound. -/
theorem be_of_stein {π : Measure E} {κ : ℝ} (hπ : PhiSobBayes.IsStronglyLogConcave π κ)
    (hκ : 0 < κ) {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ}
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ) (f : E → ℝ) (hf : f ∈ PhiSobBayes.testClass n J)
    (hSt : ∀ s : ℝ, 0 < s → ∀ θ : E,
      ‖pcov π s θ f‖ ≤ (∫ x, ‖gradient f x‖ ∂(post π s θ)) / (κ + s)) :
    PhiSobBayes.phiEnt π Φ f ≤ 1 / κ / 2 * ∫ x, deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2 ∂π := by
  have hP : IsProbabilityMeasure π := hπ.1
  obtain ⟨lo, hi, hlo, hhi, hfr⟩ := be_tc_range hf
  have hIcc : Set.Icc lo hi ⊆ J := hJ.2.1.out hlo hhi
  have hfc : Continuous f := (tc_fderiv_eq hf).choose_spec.2.2.2.continuous
  have hfm : Measurable f := hfc.measurable
  have hΦ2 : ContDiffOn ℝ 2 Φ J := hΦ.1.of_le (by norm_cast)
  set ψ := deriv (deriv Φ) with hψ
  have hψc : ContinuousOn ψ J := be_adm_d2 hJ hΦ
  have hle : lo ≤ hi := (hfr 0).1.trans (hfr 0).2
  have hexp := slc_integrable_exp_inner hπ hκ
  have hmom := slc_integrable_pow hπ hκ 4
  have hψIcc : ContinuousOn ψ (Set.Icc lo hi) := hψc.mono hIcc
  have hΦIcc : ContinuousOn Φ (Set.Icc lo hi) := hΦ.1.continuousOn.mono hIcc
  obtain ⟨Mψ, hMψ⟩ := be_bdd_comp hψIcc
  obtain ⟨MΦ, hMΦ⟩ := be_bdd_comp hΦIcc
  have hgc : Continuous (gradient f) := by
    have h := (tc_fderiv_eq hf).choose_spec.2.2.2
    have : gradient f = fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) := rfl
    rw [this]; exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp (h.continuous_fderiv (by simp))
  obtain ⟨L1, hL1⟩ := tc_gradient_bounded hf
  have hψpos : ∀ z ∈ Set.Icc lo hi, 0 < ψ z := fun z hz => hΦ.2.1 z (hIcc hz)
  set G : E → ℝ := fun x => ψ (f x) * ‖gradient f x‖ ^ 2 with hG
  have hGm : Measurable G := (be_meas_comp hle hψIcc hfm hfr).mul (hgc.measurable.norm.pow_const 2)
  have hGnn : ∀ x, 0 ≤ G x := fun x => mul_nonneg (hψpos _ (hfr x)).le (sq_nonneg _)
  have hGb : ∀ x, |G x| ≤ Mψ * L1 ^ 2 := by
    intro x
    rw [abs_of_nonneg (hGnn x)]
    have h1 : ψ (f x) ≤ Mψ := (le_abs_self _).trans (hMψ _ (hfr x))
    have h2 : ‖gradient f x‖ ^ 2 ≤ L1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hL1 x) 2
    exact mul_le_mul h1 h2 (sq_nonneg _) ((hψpos _ (hfr x)).le.trans h1)
  have hGint : ∀ (ν : Measure E) [IsFiniteMeasure ν], Integrable G ν := fun ν _ =>
    Integrable.of_bound hGm.aestronglyMeasurable _ (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hGb x)
  set Etot := ∫ x, G x ∂π with hEtot
  have hE0 : 0 ≤ Etot := integral_nonneg hGnn
  -- pointwise bound
  have hpt : ∀ s : ℝ, 0 < s → ∀ θ : E,
      ψ (pmean π s θ f) * ‖pcov π s θ f‖ ^ 2 ≤ pmean π s θ G / (κ + s) ^ 2 := by
    intro s hs θ
    have hpp := post_isProb (π := π) hs θ
    have hks : 0 < κ + s := by linarith
    set S := ∫ x, ‖gradient f x‖ ∂(post π s θ)
    have hS0 : 0 ≤ S := integral_nonneg fun x => norm_nonneg _
    have hjen := phi_jensen (post π s θ) hJ hΦ hIcc f hfm hfr (fun x => ‖gradient f x‖)
      hgc.measurable.norm ⟨L1, fun x => by rw [abs_norm]; exact hL1 x⟩
    simp only [abs_norm] at hjen
    have hpm := be_pmean_mem (π := π) hs θ hfm hfr
    have hψp := hψpos _ hpm
    have h1 : ‖pcov π s θ f‖ ^ 2 ≤ (S / (κ + s)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hSt s hs θ) 2
    calc ψ (pmean π s θ f) * ‖pcov π s θ f‖ ^ 2 ≤ ψ (pmean π s θ f) * (S / (κ + s)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hψp.le
      _ = (ψ (pmean π s θ f) * S ^ 2) / (κ + s) ^ 2 := by field_simp
      _ ≤ pmean π s θ G / (κ + s) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact hjen
  -- integrability of the dissipation integrand
  have hDint : ∀ s : ℝ, 0 < s →
      Integrable (fun θ => ψ (pmean π s θ f) * ‖pcov π s θ f‖ ^ 2) (Qt π s) := by
    intro s hs
    have := isProb_Qt (π := π) s
    refine Integrable.of_bound (((be_meas_comp hle hψIcc (measurable_pmean hs hfm)
      (fun θ => be_pmean_mem hs θ hfm hfr)).mul
      ((be_measurable_pcov π hfm hs).norm.pow_const 2))).aestronglyMeasurable
      (Mψ * (L1 / κ) ^ 2) (Filter.Eventually.of_forall fun θ => ?_)
    have hpp := post_isProb (π := π) hs θ
    have hks : 0 < κ + s := by linarith
    have hS : ∫ x, ‖gradient f x‖ ∂(post π s θ) ≤ L1 := by
      calc ∫ x, ‖gradient f x‖ ∂(post π s θ) ≤ ∫ _x, L1 ∂(post π s θ) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall hL1)
        _ = L1 := by simp
    have hL10 : 0 ≤ L1 := (norm_nonneg _).trans (hL1 0)
    have hpc : ‖pcov π s θ f‖ ≤ L1 / κ :=
      (hSt s hs θ).trans (by
        calc (∫ x, ‖gradient f x‖ ∂(post π s θ)) / (κ + s) ≤ L1 / (κ + s) :=
              div_le_div_of_nonneg_right hS hks.le
          _ ≤ L1 / κ := div_le_div_of_nonneg_left hL10 hκ (by linarith))
    have hpm := be_pmean_mem (π := π) hs θ hfm hfr
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
    exact mul_le_mul (hMψ _ hpm) (pow_le_pow_left₀ (norm_nonneg _) hpc 2) (by positivity)
      ((abs_nonneg _).trans (hMψ _ hpm))
  -- integrated dissipation bound
  have hDbound : ∀ s : ℝ, 0 < s →
      ∫ θ, ψ (pmean π s θ f) * ‖pcov π s θ f‖ ^ 2 ∂(Qt π s) ≤ Etot / (κ + s) ^ 2 := by
    intro s hs
    have := isProb_Qt (π := π) s
    calc ∫ θ, ψ (pmean π s θ f) * ‖pcov π s θ f‖ ^ 2 ∂(Qt π s)
        ≤ ∫ θ, pmean π s θ G / (κ + s) ^ 2 ∂(Qt π s) :=
          integral_mono (hDint s hs) ((integrable_pmean_Qt hs (hGint π)).div_const _) (hpt s hs)
      _ = Etot / (κ + s) ^ 2 := by rw [integral_div, integral_pmean_Qt hs G (hGint π)]
  -- the I-function and the engine in Q-form
  set I : ℝ → ℝ := fun t => ∫ θ, Φ (pmean π t θ f) ∂(Qt π t) with hI
  have hIu : ∀ t : ℝ, 0 < t → I t = ∫ u, Zt π t (Real.sqrt t • u) * Φ (pmean π t (Real.sqrt t • u) f)
      ∂(stdGaussian E) := by
    intro t ht
    have := isProb_Qt (π := π) t
    have hint : Integrable (fun θ => Φ (pmean π t θ f)) (Qt π t) :=
      Integrable.of_bound (be_meas_comp hle hΦIcc (measurable_pmean ht hfm)
        (fun θ => be_pmean_mem ht θ hfm hfr)).aestronglyMeasurable MΦ
        (Filter.Eventually.of_forall fun θ => by
          rw [Real.norm_eq_abs]; exact hMΦ _ (be_pmean_mem ht θ hfm hfr))
    simp only [hI]
    rw [integral_Qt ht _ hint]
    congr 1; funext u; ring
  have hDu : ∀ s : ℝ, 0 < s → ∫ u, Zt π s (Real.sqrt s • u) * deriv (deriv Φ)
      (pmean π s (Real.sqrt s • u) f) * ‖pcov π s (Real.sqrt s • u) f‖ ^ 2 ∂(stdGaussian E) =
      ∫ θ, ψ (pmean π s θ f) * ‖pcov π s θ f‖ ^ 2 ∂(Qt π s) := by
    intro s hs
    rw [integral_Qt hs _ (hDint s hs)]
    congr 1; funext u; simp only [hψ]; ring
  have hstep : ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ →
      I t₂ - I t₁ ≤ Etot / 2 * (1 / (κ + t₁) - 1 / (κ + t₂)) := by
    intro t₁ t₂ h1 h12
    have heng := engine_phi π hmom hJ.1 hΦ2 hfm hfr hIcc h1 h12
    rw [hIu t₂ (h1.trans_le h12), hIu t₁ h1, heng]
    have hcongr : ∫ s in t₁..t₂, (1 / 2) * ∫ u, Zt π s (Real.sqrt s • u) * deriv (deriv Φ)
        (pmean π s (Real.sqrt s • u) f) * ‖pcov π s (Real.sqrt s • u) f‖ ^ 2 ∂(stdGaussian E) =
        ∫ s in t₁..t₂, (1 / 2) * ∫ θ, ψ (pmean π s θ f) * ‖pcov π s θ f‖ ^ 2 ∂(Qt π s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le h12] at hs
      simp only
      rw [hDu s (h1.trans_le hs.1)]
    rw [hcongr]
    have hk1 : 0 < κ + t₁ := by linarith
    have hRint : IntervalIntegrable (fun s => (1 / 2) * (Etot / (κ + s) ^ 2)) volume t₁ t₂ := by
      apply ContinuousOn.intervalIntegrable
      intro s hs
      rw [Set.uIcc_of_le h12] at hs
      have hks : 0 < κ + s := by linarith [hs.1]
      exact (continuousAt_const.mul (continuousAt_const.div
        ((continuousAt_const.add continuousAt_id).pow 2) (pow_ne_zero 2 hks.ne'))).continuousWithinAt
    have hR : ∫ s in t₁..t₂, (1 / 2) * (Etot / (κ + s) ^ 2) = Etot / 2 * (1 / (κ + t₁) - 1 / (κ + t₂)) := by
      have : (fun s => (1 / 2) * (Etot / (κ + s) ^ 2)) = fun s => (Etot / 2) * (1 / (κ + s) ^ 2) := by
        funext s; ring
      rw [this, intervalIntegral.integral_const_mul, integral_inv_sq_shift hk1 h12]
    rw [← hR]
    by_cases hint : IntervalIntegrable (fun s => (1 / 2) * ∫ θ, ψ (pmean π s θ f) *
        ‖pcov π s θ f‖ ^ 2 ∂(Qt π s)) volume t₁ t₂
    · apply intervalIntegral.integral_mono_on h12 hint hRint
      intro s hs
      exact mul_le_mul_of_nonneg_left (hDbound s (h1.trans_le hs.1)) (by norm_num)
    · rw [intervalIntegral.integral_undef hint, hR]
      have : 1 / (κ + t₂) ≤ 1 / (κ + t₁) := one_div_le_one_div_of_le hk1 (by linarith)
      exact mul_nonneg (by linarith) (by linarith)
  -- limits
  have hlim0 : Tendsto I (𝓝[>] 0) (𝓝 (Φ (∫ x, f x ∂π))) :=
    tendsto_Ifun_zero_Icc hexp hfm hfr hΦIcc
  obtain ⟨Lf, hLf⟩ := be_tc_lipschitz hf
  have hlimT : Tendsto I atTop (𝓝 (∫ x, Φ (f x) ∂π)) :=
    tendsto_Ifun_top hJ.1 hΦ2 hIcc hLf hfr
  have hfin : ∀ t₁ : ℝ, 0 < t₁ → ∫ x, Φ (f x) ∂π - I t₁ ≤ Etot / 2 * (1 / (κ + t₁)) := by
    intro t₁ h1
    have hT : Tendsto (fun t₂ => I t₂ - I t₁) atTop (𝓝 (∫ x, Φ (f x) ∂π - I t₁)) :=
      hlimT.sub_const _
    refine le_of_tendsto hT ?_
    filter_upwards [eventually_ge_atTop t₁] with t₂ ht₂
    have := hstep t₁ t₂ h1 ht₂
    have h2 : 0 ≤ Etot / 2 * (1 / (κ + t₂)) := by
      apply mul_nonneg (by linarith) (by apply div_nonneg <;> linarith)
    nlinarith
  have hlimit : Tendsto (fun t₁ => ∫ x, Φ (f x) ∂π - I t₁) (𝓝[>] 0)
      (𝓝 (∫ x, Φ (f x) ∂π - Φ (∫ x, f x ∂π))) := hlim0.const_sub _
  have hRHS : Tendsto (fun t₁ : ℝ => Etot / 2 * (1 / (κ + t₁))) (𝓝[>] 0)
      (𝓝 (Etot / 2 * (1 / (κ + 0)))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    exact continuousAt_const.mul (continuousAt_const.div (continuousAt_const.add continuousAt_id)
      (by simp; exact hκ.ne'))
  have := le_of_tendsto_of_tendsto hlimit hRHS (by
    filter_upwards [self_mem_nhdsWithin] with t ht using hfin t ht)
  unfold PhiSobBayes.phiEnt
  calc _ ≤ Etot / 2 * (1 / (κ + 0)) := this
    _ = 1 / κ / 2 * Etot := by ring_nf


end PSBSL

end
end

-- ===== Fwd.lean =====
section

/-! Theorem 3.1 (forward direction) for log-concave priors, via the stochastic-localization
engine, the output Φ-Sobolev inequality and the comparison lemma `fwd_mono`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

noncomputable section
namespace PSBSL
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Fourth moment of a log-concave measure -/

section MomentA
open Set Metric

lemma fwdA_ball_sub {S : Set E} (hS : Convex ℝ S) {r : ℝ} (hr : ball (0:E) r ⊆ S) {x : E}
    (hx : x ∈ S) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1 / 2) : ball (l • x) (r / 2) ⊆ S := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  have h1 : 0 < 1 - l := by linarith
  have hr0 : 0 < r := by linarith [norm_nonneg (z - l • x)]
  set w : E := (1 - l)⁻¹ • (z - l • x) with hwdef
  have hw : w ∈ S := by
    apply hr
    rw [mem_ball, dist_zero_right, hwdef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h1,
      inv_mul_lt_iff₀ h1]
    nlinarith [mul_nonneg (sub_nonneg.2 hl1) hr0.le]
  have : z = (1 - l) • w + l • x := by
    rw [hwdef, smul_smul, mul_inv_cancel₀ h1.ne', one_smul]; abel
  rw [this]
  exact hS hw hx h1.le hl0 (by ring)

lemma fwdA_one_le_abs {k j : ℕ} (h : k ≠ j) : (1 : ℝ) ≤ |(k : ℝ) - j| := by
  rw [le_abs]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · right
    have : (k : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    linarith
  · left
    have : (j : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt h
    linarith

lemma fwdA_pack {S : Set E} (hS : Convex ℝ S) {r : ℝ} (hr0 : 0 < r) (hr : ball (0:E) r ⊆ S)
    (N : ℕ) {x : E} (hx : x ∈ S) (hxN : 2 * N * r + r ≤ ‖x‖) :
    (N : ℝ≥0∞) * volume (ball (0:E) (r / 2)) ≤ volume S := by
  have hxpos : 0 < ‖x‖ := by
    have : 0 ≤ 2 * (N : ℝ) * r := by positivity
    linarith
  set c : ℕ → E := fun k => ((k : ℝ) * r / ‖x‖) • x with hc
  have hsub : ∀ k ∈ Finset.range N, ball (c k) (r / 2) ⊆ S := by
    intro k hk
    apply fwdA_ball_sub hS hr hx (by positivity)
    rw [Finset.mem_range] at hk
    rw [div_le_iff₀ hxpos]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    nlinarith
  have hdisj : (Finset.range N : Set ℕ).PairwiseDisjoint (fun k => ball (c k) (r / 2)) := by
    intro k _ j _ hkj
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm, hc]
    simp only
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, ← sub_div, ← sub_mul, abs_div, abs_mul,
      abs_of_pos hr0, abs_of_pos hxpos, div_mul_cancel₀ _ hxpos.ne']
    have := fwdA_one_le_abs hkj
    nlinarith
  calc (N : ℝ≥0∞) * volume (ball (0:E) (r / 2))
      = ∑ k ∈ Finset.range N, volume (ball (c k) (r / 2)) := by
        simp [Measure.addHaar_ball_center]
    _ = volume (⋃ k ∈ Finset.range N, ball (c k) (r / 2)) :=
        (measure_biUnion_finset hdisj (fun k _ => measurableSet_ball)).symm
    _ ≤ volume S := measure_mono (iUnion₂_subset hsub)

lemma fwdA_vol_le {V : E → ℝ} (hV : Continuous V) {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) (M : ℝ) :
    volume {x | V x ≤ M} ≤ ENNReal.ofReal (Real.exp M) := by
  have hmeas : MeasurableSet {x | V x ≤ M} := measurableSet_le hV.measurable measurable_const
  have h1 : μ {x | V x ≤ M} ≤ 1 := prob_le_one
  rw [hμ, withDensity_apply _ hmeas] at h1
  have h2 : ∫⁻ _x in {x | V x ≤ M}, ENNReal.ofReal (Real.exp (-M)) ≤
      ∫⁻ x in {x | V x ≤ M}, ENNReal.ofReal (Real.exp (-V x)) :=
    setLIntegral_mono' hmeas (fun x hx => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (by simp only [Set.mem_ofPred_eq] at hx; linarith)))
  rw [setLIntegral_const] at h2
  have h3 : volume {x | V x ≤ M} * ENNReal.ofReal (Real.exp (-M)) ≤ 1 := by
    rw [mul_comm]; exact h2.trans h1
  calc volume {x | V x ≤ M}
      = volume {x | V x ≤ M} * ENNReal.ofReal (Real.exp (-M)) * ENNReal.ofReal (Real.exp M) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
    _ ≤ 1 * ENNReal.ofReal (Real.exp M) := by gcongr
    _ = _ := one_mul _

lemma fwdA_sublevel_bdd {V : E → ℝ} (hV : Continuous V) (hconv : ConvexOn ℝ univ V)
    {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, V x ≤ V 0 + 1 → ‖x‖ < R := by
  set M := V 0 + 1 with hM
  have hS : Convex ℝ {x | V x ≤ M} := by
    have := hconv.convex_le M
    simpa using this
  obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.1 (isOpen_lt hV continuous_const) (0 : E)
    (show V 0 < M by simp [hM])
  have hr' : ball (0:E) r ⊆ {x | V x ≤ M} := fun x hx => le_of_lt (show V x < M from hr hx)
  have hv : volume (ball (0:E) (r / 2)) ≠ 0 := (measure_ball_pos volume (0:E) (half_pos hr0)).ne'
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hv (ENNReal.ofReal_ne_top (r := Real.exp M))
  refine ⟨2 * N * r + r, by positivity, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 := fwdA_pack hS hr0 hr' N hx hcon
  have h2 := fwdA_vol_le hV hμ M
  exact absurd (h1.trans h2) (not_le.2 hN)

lemma fwdA_linear {V : E → ℝ} (hconv : ConvexOn ℝ univ V) {R : ℝ} (hR : 0 < R)
    (hS : ∀ x, V x ≤ V 0 + 1 → ‖x‖ < R) (x : E) (hx : R ≤ ‖x‖) : V 0 + ‖x‖ / R < V x := by
  have hxpos : 0 < ‖x‖ := hR.trans_le hx
  set l := R / ‖x‖ with hl
  have hl0 : 0 < l := div_pos hR hxpos
  have hl1 : l ≤ 1 := (div_le_one hxpos).2 hx
  have hy : V 0 + 1 < V (l • x) := by
    by_contra h
    push Not at h
    have := hS _ h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0, hl, div_mul_cancel₀ _ hxpos.ne'] at this
    exact lt_irrefl _ this
  have hc := hconv.2 (mem_univ x) (mem_univ (0:E)) hl0.le (sub_nonneg.2 hl1) (by ring)
  simp only [smul_zero, add_zero, smul_eq_mul] at hc
  have key : 1 < (V x - V 0) * l := by nlinarith
  have e : ‖x‖ / R = 1 / l := by rw [hl, one_div_div]
  rw [e]
  have := (div_lt_iff₀ hl0).2 key
  linarith

lemma fwdA_lower {V : E → ℝ} (hV1 : Differentiable ℝ V) (hV2 : Differentiable ℝ (fderiv ℝ V))
    (hV3 : ∀ x v, (0:ℝ) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x, a * ‖x‖ - b ≤ V x := by
  have hconv : ConvexOn ℝ univ V := by
    have := slc_convex V 0 hV1 hV2 hV3
    simpa using this
  obtain ⟨R, hR, hS⟩ := fwdA_sublevel_bdd hV1.continuous hconv hμ
  refine ⟨1 / R, -V 0 + ‖fderiv ℝ V 0‖ * R + 1, by positivity, fun x => ?_⟩
  rcases le_or_gt R ‖x‖ with hx | hx
  · have := fwdA_linear hconv hR hS x hx
    have h0 : 0 ≤ ‖fderiv ℝ V 0‖ * R := by positivity
    rw [one_div_mul_eq_div]
    linarith
  · have ht := slc_quadratic_lower V 0 hV1 hV2 hV3 0 x
    simp only [sub_zero, zero_div, zero_mul, add_zero] at ht
    have h1 : -(‖fderiv ℝ V 0‖ * ‖x‖) ≤ fderiv ℝ V 0 x := by
      have := (fderiv ℝ V 0).le_opNorm x
      rw [Real.norm_eq_abs] at this
      exact neg_le_of_abs_le this
    have h2 : ‖fderiv ℝ V 0‖ * ‖x‖ ≤ ‖fderiv ℝ V 0‖ * R :=
      mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)
    have h3 : 1 / R * ‖x‖ ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hR]; exact hx.le
    linarith

lemma fwdA_poly_exp {a : ℝ} (ha : 0 < a) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ m * Real.exp (-(a * r)) ≤ m.factorial * Real.exp a / a ^ m := by
  have h := Real.pow_div_factorial_le_exp (a * (1 + r)) (by positivity) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf, mul_pow] at h
  have he : Real.exp (a * (1 + r)) = Real.exp a * Real.exp (a * r) := by
    rw [← Real.exp_add]; ring_nf
  rw [he] at h
  have hexp : Real.exp (-(a * r)) * Real.exp (a * r) = 1 := by
    rw [← Real.exp_add]; simp
  rw [le_div_iff₀ (by positivity)]
  have hpos : 0 < Real.exp (-(a * r)) := Real.exp_pos _
  calc (1 + r) ^ m * Real.exp (-(a * r)) * a ^ m
      = Real.exp (-(a * r)) * (a ^ m * (1 + r) ^ m) := by ring
    _ ≤ Real.exp (-(a * r)) * (Real.exp a * Real.exp (a * r) * m.factorial) :=
        mul_le_mul_of_nonneg_left h hpos.le
    _ = m.factorial * Real.exp a * (Real.exp (-(a * r)) * Real.exp (a * r)) := by ring
    _ = m.factorial * Real.exp a := by rw [hexp, mul_one]

theorem fwd_lc_moment {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : PhiSobBayes.IsLogConcave μ) : Integrable (fun x => ‖x‖ ^ 4) μ := by
  obtain ⟨hP, V, hV1, hV2, hV3, hμeq⟩ := hμ
  have hV3' : ∀ x v, (0:ℝ) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v := by simpa using hV3
  obtain ⟨a, b, ha, hab⟩ := fwdA_lower hV1 hV2 hV3' hμeq
  rw [hμeq, integrable_withDensity_iff_integrable_smul' (show Measurable (fun x : E => ENNReal.ofReal (Real.exp (-V x))) from hV1.continuous.measurable.neg.exp.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  set m := n + 5
  set K := Real.exp b * (m.factorial * Real.exp a / a ^ m)
  have hint := (integrable_one_add_norm (μ := (volume : Measure E)) (r := (n : ℝ) + 1)
    (by simp)).const_mul K
  refine hint.mono' ((hV1.continuous.neg.rexp.mul (continuous_norm.pow 4)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  set r := ‖x‖ with hrdef
  have hr : 0 ≤ r := norm_nonneg _
  have h1r : 0 < 1 + r := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hrp : (1 + r) ^ (-((n : ℝ) + 1)) = ((1 + r) ^ (n + 1))⁻¹ := by
    rw [Real.rpow_neg h1r.le, ← Real.rpow_natCast]; push_cast; ring_nf
  rw [hrp, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hV : Real.exp (-V x) ≤ Real.exp b * Real.exp (-(a * r)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; linarith [hab x]
  have hr4 : r ^ 4 ≤ (1 + r) ^ 4 := pow_le_pow_left₀ hr (by linarith) 4
  have hpe := fwdA_poly_exp ha m hr
  calc Real.exp (-V x) * r ^ 4 * (1 + r) ^ (n + 1)
      ≤ Real.exp b * Real.exp (-(a * r)) * (1 + r) ^ 4 * (1 + r) ^ (n + 1) := by gcongr
    _ = Real.exp b * ((1 + r) ^ m * Real.exp (-(a * r))) := by
        simp only [m]; ring
    _ ≤ K := mul_le_mul_of_nonneg_left hpe (Real.exp_pos _).le

end MomentA

/-! ### Smoothness of the posterior mean -/

section SmoothC

def fwdC_A (μ : Measure E) (s : ℝ) (c : E → ℝ) (θ : E) : ℝ := ∫ x, c x * wt s θ x ∂μ

def fwdC_B (μ : Measure E) (s : ℝ) (c : E → ℝ) (θ : E) : E := ∫ x, (c x * wt s θ x) • x ∂μ

lemma fwdC_quad {s : ℝ} (hs : 0 < s) (a r : ℝ) : a * r - s * r ^ 2 / 2 ≤ a ^ 2 / (2 * s) := by
  have h : a ^ 2 / (2 * s) - (a * r - s * r ^ 2 / 2) = (a - s * r) ^ 2 / (2 * s) := by
    field_simp; ring
  have : 0 ≤ (a - s * r) ^ 2 / (2 * s) := by positivity
  linarith

lemma fwdC_inner_le {R : ℝ} (θ x : E) (hθ : ‖θ‖ ≤ R) : ⟪θ, x⟫ ≤ R * ‖x‖ :=
  (real_inner_le_norm θ x).trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _))

lemma fwdC_wt_le {s : ℝ} (hs : 0 < s) {R : ℝ} (θ x : E) (hθ : ‖θ‖ ≤ R) :
    wt s θ x ≤ Real.exp (R ^ 2 / (2 * s)) := by
  unfold wt
  apply Real.exp_le_exp.2
  have h1 := fwdC_inner_le θ x hθ
  have := fwdC_quad hs R ‖x‖
  linarith

lemma fwdC_wt_norm_le {s : ℝ} (hs : 0 < s) {R : ℝ} (θ x : E) (hθ : ‖θ‖ ≤ R) :
    wt s θ x * ‖x‖ ≤ Real.exp ((R + 1) ^ 2 / (2 * s)) := by
  have hx : ‖x‖ ≤ Real.exp ‖x‖ := by linarith [Real.add_one_le_exp ‖x‖]
  calc wt s θ x * ‖x‖ ≤ wt s θ x * Real.exp ‖x‖ := mul_le_mul_of_nonneg_left hx (wt_nonneg _ _ _)
    _ = Real.exp (⟪θ, x⟫ - s * ‖x‖ ^ 2 / 2 + ‖x‖) := by unfold wt; rw [Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have h1 := fwdC_inner_le θ x hθ
      have := fwdC_quad hs (R + 1) ‖x‖
      have e : (R + 1) * ‖x‖ = R * ‖x‖ + ‖x‖ := by ring
      linarith

section
variable (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] {c : EuclideanSpace ℝ (Fin n) → ℝ} (hc : Measurable c) {K : ℝ}
  (hK : ∀ x, |c x| ≤ K) {s : ℝ} (hs : 0 < s)

include hc hK hs in
lemma fwdC_int_A (θ : E) : Integrable (fun x => c x * wt s θ x) μ := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  refine Integrable.of_bound (hc.mul (measurable_wt_right s θ)).aestronglyMeasurable
    (K * Real.exp (‖θ‖ ^ 2 / (2 * s))) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos s θ x)]
  exact mul_le_mul (hK x) (fwdC_wt_le hs θ x le_rfl) (wt_nonneg _ _ _) hK0

include hc hK hs in
lemma fwdC_int_B (θ : E) : Integrable (fun x => (c x * wt s θ x) • x) μ := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  refine Integrable.of_bound ((hc.mul (measurable_wt_right s θ)).smul measurable_id).aestronglyMeasurable
    (K * Real.exp ((‖θ‖ + 1) ^ 2 / (2 * s))) (Eventually.of_forall fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos s θ x), mul_assoc]
  exact mul_le_mul (hK x) (fwdC_wt_norm_le hs θ x le_rfl) (mul_nonneg (wt_nonneg _ _ _) (norm_nonneg _)) hK0

lemma fwdC_hasFDerivAt_wt (s : ℝ) (θ x : E) :
    HasFDerivAt (fun θ => wt s θ x) (wt s θ x • innerSL ℝ x) θ := by
  have h1 : HasFDerivAt (fun θ : E => ⟪θ, x⟫ - s * ‖x‖ ^ 2 / 2) (innerSL ℝ x) θ := by
    have : (fun θ : E => ⟪θ, x⟫ - s * ‖x‖ ^ 2 / 2) = fun θ => innerSL ℝ x θ - s * ‖x‖ ^ 2 / 2 := by
      funext θ; simp [real_inner_comm]
    rw [this]
    exact (innerSL ℝ x).hasFDerivAt.sub_const _
  unfold wt
  exact h1.exp

include hc hK hs in
lemma fwdC_hasFDerivAt_A (θ₀ : E) :
    HasFDerivAt (fwdC_A μ s c) (innerSL ℝ (fwdC_B μ s c θ₀)) θ₀ := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hmeas : AEStronglyMeasurable (fun x => (c x * wt s θ₀ x) • innerSL ℝ x) μ :=
    ((hc.mul (measurable_wt_right s θ₀)).smul (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.measurable).aestronglyMeasurable
  have hbd : ∀ᵐ x ∂μ, ∀ θ ∈ Metric.ball θ₀ 1,
      ‖(c x * wt s θ x) • innerSL ℝ x‖ ≤ K * Real.exp ((‖θ₀‖ + 1 + 1) ^ 2 / (2 * s)) := by
    refine Eventually.of_forall fun x θ hθ => ?_
    have hθR : ‖θ‖ ≤ ‖θ₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' θ θ₀
      rw [Metric.mem_ball, dist_eq_norm] at hθ
      linarith
    rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos s θ x), mul_assoc]
    exact mul_le_mul (hK x) (fwdC_wt_norm_le hs θ x hθR) (mul_nonneg (wt_nonneg _ _ _) (norm_nonneg _)) hK0
  have hder : ∀ᵐ x ∂μ, ∀ θ ∈ Metric.ball θ₀ 1,
      HasFDerivAt (fun θ => c x * wt s θ x) ((c x * wt s θ x) • innerSL ℝ x) θ := by
    refine Eventually.of_forall fun x θ _ => ?_
    have := (fwdC_hasFDerivAt_wt s θ x).const_mul (c x)
    rwa [smul_smul] at this
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
    (F := fun θ x => c x * wt s θ x) (F' := fun θ x => (c x * wt s θ x) • innerSL ℝ x)
    (x₀ := θ₀) (bound := fun _ => K * Real.exp ((‖θ₀‖ + 1 + 1) ^ 2 / (2 * s)))
    (Metric.ball_mem_nhds θ₀ one_pos)
    (Eventually.of_forall fun θ => (fwdC_int_A μ hc hK hs θ).aestronglyMeasurable)
    (fwdC_int_A μ hc hK hs θ₀) hmeas hbd (integrable_const _) hder
  have e : ∫ x, (c x * wt s θ₀ x) • innerSL ℝ x ∂μ = innerSL ℝ (fwdC_B μ s c θ₀) := by
    unfold fwdC_B
    rw [← ContinuousLinearMap.integral_comp_comm _ (fwdC_int_B μ hc hK hs θ₀)]
    congr 1; funext x; simp
  rw [e] at key
  exact key

include hc hK hs in
lemma fwdC_continuous_B : Continuous (fwdC_B μ s c) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  rw [continuous_iff_continuousAt]
  intro θ₀
  refine continuousAt_of_dominated (bound := fun _ => K * Real.exp ((‖θ₀‖ + 1 + 1) ^ 2 / (2 * s)))
    (Eventually.of_forall fun θ => (fwdC_int_B μ hc hK hs θ).aestronglyMeasurable) ?_
    (integrable_const _) (Eventually.of_forall fun x => ?_)
  · filter_upwards [Metric.ball_mem_nhds θ₀ one_pos] with θ hθ
    refine Eventually.of_forall fun x => ?_
    have hθR : ‖θ‖ ≤ ‖θ₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' θ θ₀
      rw [Metric.mem_ball, dist_eq_norm] at hθ
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos s θ x), mul_assoc]
    exact mul_le_mul (hK x) (fwdC_wt_norm_le hs θ x hθR) (mul_nonneg (wt_nonneg _ _ _) (norm_nonneg _)) hK0
  · exact (((fwdC_hasFDerivAt_wt s θ₀ x).continuousAt.const_mul (c x)).smul continuousAt_const)

end

variable (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {K : ℝ}
  (hK : ∀ x, |f x| ≤ K) {s : ℝ} (hs : 0 < s)

omit [IsProbabilityMeasure μ] in
lemma fwdC_A_one (θ : E) : fwdC_A μ s (fun _ => 1) θ = Zt μ s θ := by
  simp [fwdC_A, Zt]

omit [IsProbabilityMeasure μ] in
lemma fwdC_pmean_eq : (fun θ => pmean μ s θ f) = fun θ => fwdC_A μ s f θ * (fwdC_A μ s (fun _ => 1) θ)⁻¹ := by
  funext θ
  rw [pmean_eq, fwdC_A_one, div_eq_mul_inv]; rfl

include hf hK hs in
lemma fwdC_pcov_eq (θ : E) : pcov μ s θ f =
    (Zt μ s θ)⁻¹ • (fwdC_B μ s f θ - pmean μ s θ f • fwdC_B μ s (fun _ => 1) θ) := by
  rw [eng_pcov_eq]
  congr 1
  set m := pmean μ s θ f
  have e : ∀ x, wt s θ x • ((f x - m) • x) = (f x * wt s θ x) • x - m • ((1 * wt s θ x) • x) := by
    intro x; simp only [smul_smul]; rw [← sub_smul]; congr 1; ring
  simp_rw [e]
  have h1 : ∀ x, |(fun _ : E => (1:ℝ)) x| ≤ 1 := fun x => by simp
  have h2 : Integrable (fun x => m • ((1 * wt s θ x) • x)) μ :=
    (fwdC_int_B μ measurable_const h1 hs θ).smul m
  rw [integral_sub (fwdC_int_B μ hf hK hs θ) h2, integral_smul]
  rfl

include hf hK hs in
theorem fwd_pmean_hasFDerivAt (θ : E) :
    HasFDerivAt (fun θ => pmean μ s θ f) (innerSL ℝ (pcov μ s θ f)) θ := by
  have h1 : ∀ x, |(fun _ : E => (1:ℝ)) x| ≤ 1 := fun x => by simp
  have hA := fwdC_hasFDerivAt_A μ hf hK hs θ
  have hZ := fwdC_hasFDerivAt_A μ measurable_const h1 hs θ
  have hZpos : 0 < fwdC_A μ s (fun _ => 1) θ := by rw [fwdC_A_one]; exact Zt_pos hs θ
  have hinv := (hasDerivAt_inv hZpos.ne').comp_hasFDerivAt θ hZ
  have hm := hA.mul hinv
  have hfun : (fun θ => pmean μ s θ f) =
      fwdC_A μ s f * ((fun x => x⁻¹) ∘ fwdC_A μ s (fun _ => 1)) := by
    rw [fwdC_pmean_eq]; rfl
  rw [hfun]
  refine hm.congr_fderiv ?_
  rw [fwdC_pcov_eq μ hf hK hs θ, ← fwdC_A_one μ θ]
  have hpm : pmean μ s θ f = fwdC_A μ s f θ * (fwdC_A μ s (fun _ => 1) θ)⁻¹ :=
    congrFun (fwdC_pmean_eq μ) θ
  rw [hpm]
  ext v
  simp only [map_smul, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul, innerSL_apply_apply, Function.comp_apply]
  field_simp
  ring

include hf hK hs in
theorem fwd_pcov_continuous : Continuous (fun θ => pcov μ s θ f) := by
  have h1 : ∀ x, |(fun _ : E => (1:ℝ)) x| ≤ 1 := fun x => by simp
  have hZc : Continuous (Zt μ s) := continuous_Zt hs
  have hpm : Continuous (fun θ => pmean μ s θ f) := by
    rw [continuous_iff_continuousAt]
    intro θ; exact (fwd_pmean_hasFDerivAt μ hf hK hs θ).continuousAt
  have : (fun θ => pcov μ s θ f) = fun θ =>
      (Zt μ s θ)⁻¹ • (fwdC_B μ s f θ - pmean μ s θ f • fwdC_B μ s (fun _ => 1) θ) := by
    funext θ; exact fwdC_pcov_eq μ hf hK hs θ
  rw [this]
  exact (hZc.inv₀ fun θ => (Zt_pos hs θ).ne').smul ((fwdC_continuous_B μ hf hK hs).sub
    (hpm.smul (fwdC_continuous_B μ measurable_const h1 hs)))

include hf hK hs in
theorem fwd_pmean_contDiff : ContDiff ℝ 1 (fun θ => pmean μ s θ f) :=
  contDiff_one_iff_hasFDerivAt.2 ⟨fun θ => innerSL ℝ (pcov μ s θ f),
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.comp (fwd_pcov_continuous μ hf hK hs),
    fun θ => fwd_pmean_hasFDerivAt μ hf hK hs θ⟩

include hf hK hs in
theorem fwd_gradient_pmean (θ : E) :
    gradient (fun θ => pmean μ s θ f) θ = pcov μ s θ f := by
  unfold gradient
  rw [(fwd_pmean_hasFDerivAt μ hf hK hs θ).fderiv, LinearIsometryEquiv.symm_apply_eq]
  ext v
  simp

end SmoothC

/-! ### The standard Gaussian is 1-strongly log-concave -/

lemma fwd_gauss_hasFDerivAt (x : E) :
    HasFDerivAt (fun x : E => ‖x‖ ^ 2 / 2 + (n / 2 : ℝ) * Real.log (2 * Real.pi))
      (innerSL ℝ x) x := by
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (1/2 : ℝ)).add_const
    ((n / 2 : ℝ) * Real.log (2 * Real.pi))
  have e1 : (fun x : E => ‖x‖ ^ 2 / 2 + (n / 2 : ℝ) * Real.log (2 * Real.pi)) =
      fun x => 1 / 2 * ‖x‖ ^ 2 + (n / 2 : ℝ) * Real.log (2 * Real.pi) := by funext y; ring
  have e2 : innerSL ℝ x = (1 / 2 : ℝ) • (2 : ℕ) • innerSL ℝ x := by
    ext v; simp
  rw [e1, e2]; exact h

lemma fwd_gauss_fderiv :
    fderiv ℝ (fun x : E => ‖x‖ ^ 2 / 2 + (n / 2 : ℝ) * Real.log (2 * Real.pi)) = innerSL ℝ := by
  funext x; exact (fwd_gauss_hasFDerivAt x).fderiv

theorem fwd_gauss_slc : PhiSobBayes.IsStronglyLogConcave (stdGaussian E) 1 := by
  refine ⟨inferInstance, fun x : E => ‖x‖ ^ 2 / 2 + (n / 2 : ℝ) * Real.log (2 * Real.pi),
    fun x => (fwd_gauss_hasFDerivAt x).differentiableAt, ?_, ?_, ?_⟩
  · rw [fwd_gauss_fderiv]; exact (innerSL ℝ).differentiable
  · intro x v
    rw [fwd_gauss_fderiv, ContinuousLinearMap.fderiv]
    simp only [one_mul]
    change ‖v‖ ^ 2 ≤ ⟪v, v⟫
    rw [real_inner_self_eq_norm_sq]
  · rw [stdGaussian_eq_withDensity]
    congr 1; funext g
    unfold gaussDens
    congr 1
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
    congr 1; ring

/-! ### Posterior covariance bound -/

lemma fwd_post_slc {μ : Measure E} (hμ : PhiSobBayes.IsLogConcave μ) {s : ℝ} (hs : 0 < s)
    (θ : E) : PhiSobBayes.IsStronglyLogConcave (post μ s θ) s := by
  have h := PhiSobBayes.lemma_6_1 μ hμ s hs ((Real.sqrt s)⁻¹ • θ)
  rw [posterior_eq_post μ s hs.le, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hs).ne',
    one_smul] at h
  exact h

lemma fwd_pcov_bound {μ : Measure E} (hμ : PhiSobBayes.IsLogConcave μ) {f : E → ℝ}
    (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) {s : ℝ} (hs : 0 < s) (θ : E) :
    ‖pcov μ s θ f‖ ≤ K * (1 + n / s) := by
  have hP := fwd_post_slc hμ hs θ
  set P := post μ s θ with hPdef
  have hprob : IsProbabilityMeasure P := hP.1
  set m := pmean μ s θ f with hm
  set c : E := ∫ y, y ∂P with hc
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hfi : Integrable f P := Integrable.of_bound hf.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK x)
  have hgi : Integrable (fun x => f x - m) P := hfi.sub (integrable_const _)
  have hg0 : ∫ x, (f x - m) ∂P = 0 := by
    rw [integral_sub hfi (integrable_const _)]
    simp [hm, pmean, hPdef]
  have hgb : ∀ x, |f x - m| ≤ 2 * K := by
    intro x
    have hmK : |m| ≤ K := by
      rw [hm, pmean, ← hPdef]
      calc |∫ x, f x ∂P| = ‖∫ x, f x ∂P‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x, ‖f x‖ ∂P := norm_integral_le_integral_norm _
        _ ≤ ∫ _x, K ∂P := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun x => by
              show ‖f x‖ ≤ K
              rw [Real.norm_eq_abs]; exact hK x)
        _ = K := by simp
    calc |f x - m| ≤ |f x| + |m| := abs_sub _ _
      _ ≤ 2 * K := by linarith [hK x]
  have hid : Integrable (fun x : E => x) P := slc_integrable_id hP hs
  have h2 := slc_integrable_pow hP hs 2
  have hxc : Integrable (fun x : E => x - c) P := hid.sub (integrable_const _)
  have hgx : Integrable (fun x => (f x - m) • x) P :=
    (hid.norm.const_mul (2 * K)).mono' (hgi.aestronglyMeasurable.smul hid.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _))
  have hgc : Integrable (fun x => (f x - m) • c) P := hgi.smul_const c
  have heq : pcov μ s θ f = ∫ x, (f x - m) • (x - c) ∂P := by
    have : (fun x => (f x - m) • (x - c)) = fun x => (f x - m) • x - (f x - m) • c := by
      funext x; rw [smul_sub]
    rw [this, integral_sub hgx hgc, integral_smul_const, hg0, zero_smul, sub_zero]
    rfl
  have hsq : Integrable (fun x => ‖x - c‖ ^ 2) P := by
    refine Integrable.mono' ((h2.const_mul 2).add (integrable_const (2 * ‖c‖ ^ 2)))
      (hxc.norm.aestronglyMeasurable.pow 2) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := norm_sub_le x c
    have h4 : ‖x - c‖ ^ 2 ≤ (‖x‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖x‖ - ‖c‖)]
  have hvar : ∫ x, ‖x - c‖ ^ 2 ∂P ≤ n / s := slc_second_moment hP hs
  rw [heq]
  calc ‖∫ x, (f x - m) • (x - c) ∂P‖ ≤ ∫ x, K * (1 + ‖x - c‖ ^ 2) ∂P := by
        refine norm_integral_le_of_norm_le (((integrable_const 1).add hsq).const_mul K)
          (Filter.Eventually.of_forall fun x => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        have h1 := hgb x
        have h0 := norm_nonneg (x - c)
        nlinarith [sq_nonneg (‖x - c‖ - 1), abs_nonneg (f x - m)]
    _ = K * (1 + ∫ x, ‖x - c‖ ^ 2 ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const _) hsq]; simp
    _ ≤ K * (1 + n / s) := by gcongr

/-! ### The comparison argument -/

/-- `K(t) = Ent^Φ_{Q_t}(pmean) ≤ C t/(1 + C t) Ent^Φ_μ(f)`. -/
theorem fwd_K_le {μ : Measure E} (hμ : PhiSobBayes.IsLogConcave μ) {C : ℝ} (hC : 0 < C)
    {J : Set ℝ} (hJ : PhiSobBayes.IsOpenInterval J) {Φ : ℝ → ℝ} (hΦ : PhiSobBayes.AdmissiblePhi J Φ)
    (hS : PhiSobBayes.PhiSobolev μ J Φ C) {f : E → ℝ} (hf : f ∈ PhiSobBayes.testClass n J)
    {t : ℝ} (ht : 0 < t) :
    PhiSobBayes.phiEnt (Qt μ t) Φ (fun θ => pmean μ t θ f) ≤
      C * t / (1 + C * t) * PhiSobBayes.phiEnt μ Φ f := by
  have hP : IsProbabilityMeasure μ := hμ.1
  have hmom := fwd_lc_moment hμ
  obtain ⟨lo, hi, hlo, hhi, hfr⟩ := be_tc_range hf
  have hIcc : Set.Icc lo hi ⊆ J := hJ.2.1.out hlo hhi
  have hfc : Continuous f := (tc_fderiv_eq hf).choose_spec.2.2.2.continuous
  have hfm : Measurable f := hfc.measurable
  have hle : lo ≤ hi := (hfr 0).1.trans (hfr 0).2
  have hΦ2 : ContDiffOn ℝ 2 Φ J := hΦ.1.of_le (by norm_cast)
  set ψ := deriv (deriv Φ) with hψ
  have hψc : ContinuousOn ψ J := be_adm_d2 hJ hΦ
  have hψIcc : ContinuousOn ψ (Set.Icc lo hi) := hψc.mono hIcc
  have hΦIcc : ContinuousOn Φ (Set.Icc lo hi) := hΦ.1.continuousOn.mono hIcc
  obtain ⟨Mψ, hMψ⟩ := be_bdd_comp hψIcc
  obtain ⟨MΦ, hMΦ⟩ := be_bdd_comp hΦIcc
  set K0 := max |lo| |hi| with hK0
  have hfK : ∀ x, |f x| ≤ K0 := fun x => by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le lo, le_max_left |lo| |hi|, (hfr x).1]
    · linarith [le_abs_self hi, le_max_right |lo| |hi|, (hfr x).2]
  have hK00 : 0 ≤ K0 := (abs_nonneg _).trans (hfK 0)
  have hMψ0 : 0 ≤ Mψ := (abs_nonneg _).trans (hMψ lo ⟨le_rfl, hle⟩)
  have hfint : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable K0
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfK x)
  -- the clamped second derivative
  set ψc : ℝ → ℝ := fun z => ψ (Set.projIcc lo hi hle z) with hψcdef
  have hψcc : Continuous ψc := hψIcc.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun z => (Set.projIcc lo hi hle z).2)
  have hψcψ : ∀ z ∈ Set.Icc lo hi, ψc z = ψ z := fun z hz => by
    simp [hψcdef, Set.projIcc_of_mem hle hz]
  -- the bound on the posterior covariance
  set Bp : ℝ → ℝ := fun s => K0 * (1 + n / s) with hBp
  have hpcov : ∀ s, 0 < s → ∀ θ, ‖pcov μ s θ f‖ ≤ Bp s := fun s hs θ =>
    fwd_pcov_bound hμ hfm hfK hs θ
  have hBp_anti : ∀ s₁ s, 0 < s₁ → s₁ ≤ s → Bp s ≤ Bp s₁ := by
    intro s₁ s h1 h
    simp only [hBp]
    apply mul_le_mul_of_nonneg_left _ hK00
    have : (n : ℝ) / s ≤ n / s₁ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) h1 h
    linarith
  -- dissipation in θ-form
  have hDint : ∀ s : ℝ, 0 < s →
      Integrable (fun θ => ψ (pmean μ s θ f) * ‖pcov μ s θ f‖ ^ 2) (Qt μ s) := by
    intro s hs
    have := isProb_Qt (π := μ) s
    refine Integrable.of_bound (((be_meas_comp hle hψIcc (measurable_pmean hs hfm)
      (fun θ => be_pmean_mem hs θ hfm hfr)).mul
      ((be_measurable_pcov μ hfm hs).norm.pow_const 2))).aestronglyMeasurable
      (Mψ * Bp s ^ 2) (Eventually.of_forall fun θ => ?_)
    have hpm := be_pmean_mem (π := μ) hs θ hfm hfr
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
    exact mul_le_mul (hMψ _ hpm) (pow_le_pow_left₀ (norm_nonneg _) (hpcov s hs θ) 2)
      (by positivity) hMψ0
  -- dissipation in u-form (with the clamp, defined for every `s`)
  set D : ℝ → ℝ := fun s => ∫ u, Zt μ s (Real.sqrt s • u) *
      ψc (pmean μ s (Real.sqrt s • u) f) * ‖pcov μ s (Real.sqrt s • u) f‖ ^ 2
      ∂(stdGaussian E) with hDdef
  have hDmeas : Measurable D := by
    have hF : Measurable (fun p : ℝ × E => Zt μ p.1 (Real.sqrt p.1 • p.2) *
        ψc (pmean μ p.1 (Real.sqrt p.1 • p.2) f) * ‖pcov μ p.1 (Real.sqrt p.1 • p.2) f‖ ^ 2) :=
      ((eng_measurable_Zt μ).mul (hψcc.measurable.comp (eng_measurable_pmean μ hfm))).mul
        ((eng_measurable_pcov μ hfm).norm.pow_const 2)
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGaussian E)).measurable
  have hDu : ∀ s : ℝ, 0 < s →
      D s = ∫ θ, ψ (pmean μ s θ f) * ‖pcov μ s θ f‖ ^ 2 ∂(Qt μ s) := by
    intro s hs
    rw [integral_Qt hs _ (hDint s hs)]
    simp only [hDdef]
    congr 1; funext u
    rw [hψcψ _ (be_pmean_mem hs _ hfm hfr)]
    ring
  have hDbd : ∀ s : ℝ, 0 < s → ‖D s‖ ≤ Mψ * Bp s ^ 2 := by
    intro s hs
    have := isProb_Qt (π := μ) s
    rw [hDu s hs]
    calc ‖∫ θ, ψ (pmean μ s θ f) * ‖pcov μ s θ f‖ ^ 2 ∂(Qt μ s)‖
        ≤ (Mψ * Bp s ^ 2) * (Qt μ s Set.univ).toReal := by
          refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun θ => ?_)
          have hpm := be_pmean_mem (π := μ) hs θ hfm hfr
          rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
          exact mul_le_mul (hMψ _ hpm) (pow_le_pow_left₀ (norm_nonneg _) (hpcov s hs θ) 2)
            (by positivity) hMψ0
      _ = Mψ * Bp s ^ 2 := by simp
  have hDii : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      IntervalIntegrable (fun s => (1 / 2 : ℝ) * D s) volume s₁ s₂ := by
    intro s₁ s₂ h1 h12
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h12]
    refine Measure.integrableOn_of_bounded (M := (1 / 2 : ℝ) * (Mψ * Bp s₁ ^ 2))
      (by simp) (measurable_const.mul hDmeas).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun s hs => ?_
    have hs0 : 0 < s := h1.trans hs.1
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine (hDbd s hs0).trans (mul_le_mul_of_nonneg_left ?_ hMψ0)
    have hb := hBp_anti s₁ s h1 hs.1.le
    have hb0 : 0 ≤ Bp s := (norm_nonneg _).trans (hpcov s hs0 0)
    exact pow_le_pow_left₀ hb0 hb 2
  -- the I-function and the engine
  set I : ℝ → ℝ := fun s => ∫ θ, Φ (pmean μ s θ f) ∂(Qt μ s) with hI
  have hIu : ∀ s : ℝ, 0 < s → I s = ∫ u, Zt μ s (Real.sqrt s • u) *
      Φ (pmean μ s (Real.sqrt s • u) f) ∂(stdGaussian E) := by
    intro s hs
    have := isProb_Qt (π := μ) s
    have hint : Integrable (fun θ => Φ (pmean μ s θ f)) (Qt μ s) :=
      Integrable.of_bound (be_meas_comp hle hΦIcc (measurable_pmean hs hfm)
        (fun θ => be_pmean_mem hs θ hfm hfr)).aestronglyMeasurable MΦ
        (Eventually.of_forall fun θ => by
          rw [Real.norm_eq_abs]; exact hMΦ _ (be_pmean_mem hs θ hfm hfr))
    simp only [hI]
    rw [integral_Qt hs _ hint]
    congr 1; funext u; ring
  have hstep : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      I s₂ - I s₁ = ∫ s in s₁..s₂, (1 / 2 : ℝ) * D s := by
    intro s₁ s₂ h1 h12
    have heng := engine_phi μ hmom hJ.1 hΦ2 hfm hfr hIcc h1 h12
    rw [hIu s₂ (h1.trans_le h12), hIu s₁ h1, heng]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le h12] at hs
    have hs0 : 0 < s := h1.trans_le hs.1
    simp only [hDdef]
    congr 2; funext u
    rw [hψcψ _ (be_pmean_mem hs0 _ hfm hfr)]
  -- K and the output Φ-Sobolev inequality
  set m0 := ∫ x, f x ∂μ with hm0
  set Kf : ℝ → ℝ := fun s => I s - Φ m0 with hKf
  have hKphi : ∀ s : ℝ, 0 < s →
      PhiSobBayes.phiEnt (Qt μ s) Φ (fun θ => pmean μ s θ f) = Kf s := by
    intro s hs
    unfold PhiSobBayes.phiEnt
    rw [integral_pmean_Qt hs f hfint]
  have hG : PhiSobBayes.PhiSobolev (stdGaussian E) J Φ 1 := by
    have := (PhiSobBayes.fact_A_22 (stdGaussian E) 1 one_pos fwd_gauss_slc).2.2 J Φ hJ hΦ
    simpa using this
  have hKD : ∀ s : ℝ, 0 < s → Kf s ≤ (C * s ^ 2 + s) / 2 * D s := by
    intro s hs
    have hos := phiSobolev_Qt μ hJ hΦ hC.le hS hG hIcc (fun θ => pmean μ s θ f)
      (fwd_pmean_contDiff μ hfm hfK hs) (fun θ => be_pmean_mem hs θ hfm hfr)
      ⟨Bp s, fun θ => by rw [fwd_gradient_pmean μ hfm hfK hs θ]; exact hpcov s hs θ⟩ s hs
    rw [hKphi s hs] at hos
    rw [hDu s hs]
    simpa only [fwd_gradient_pmean μ hfm hfK hs] using hos
  -- Lipschitz bound on K on [t, ∞)
  set B := (1 / 2 : ℝ) * (Mψ * Bp t ^ 2) with hB
  have hKlip : ∀ s₁ s₂ : ℝ, t ≤ s₁ → s₁ ≤ s₂ → |Kf s₂ - Kf s₁| ≤ B * (s₂ - s₁) := by
    intro s₁ s₂ h1 h12
    have hs1 : 0 < s₁ := ht.trans_le h1
    have : Kf s₂ - Kf s₁ = I s₂ - I s₁ := by simp only [hKf]; ring
    rw [this, hstep s₁ s₂ hs1 h12, ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s₁) (b := s₂) (C := B)
      (f := fun s => (1 / 2 : ℝ) * D s) (by
        intro s hs
        rw [Set.uIoc_of_le h12] at hs
        have hs0 : 0 < s := hs1.trans hs.1
        rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), hB]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine (hDbd s hs0).trans (mul_le_mul_of_nonneg_left ?_ hMψ0)
        have hb := hBp_anti t s ht (h1.trans hs.1.le)
        have hb0 : 0 ≤ Bp s := (norm_nonneg _).trans (hpcov s hs0 0)
        exact pow_le_pow_left₀ hb0 hb 2)
    rwa [abs_of_nonneg (by linarith)] at this
  have hB0 : 0 ≤ B := by positivity
  have hKcont : ∀ T, ContinuousOn Kf (Set.Icc t T) := by
    intro T
    refine (LipschitzOnWith.of_dist_le_mul (K := B.toNNReal) fun x hx y hy => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hB0]
    rcases le_total x y with h | h
    · rw [abs_sub_comm (Kf x), abs_sub_comm x y, abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
      exact hKlip x y hx.1 h
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
      exact hKlip y x hy.1 h
  -- the comparison lemma
  have hmono : ∀ T, t ≤ T → Kf t * ((1 + C * t) / t) ≤ Kf T * ((1 + C * T) / T) := by
    intro T hT
    refine fwd_mono hC.le ht hT Kf (hKcont T) ?_
    intro s₁ s₂ h1 h12 h2
    have hs1 : 0 < s₁ := ht.trans_le h1
    have : Kf s₂ - Kf s₁ = I s₂ - I s₁ := by simp only [hKf]; ring
    rw [this, hstep s₁ s₂ hs1 h12]
    have hcK : ContinuousOn (fun s => Kf s / (s * (1 + C * s))) (Set.Icc s₁ s₂) := by
      refine ((hKcont T).mono (Set.Icc_subset_Icc h1 h2)).div (by fun_prop) ?_
      intro s hs
      have : 0 < s := hs1.trans_le hs.1
      positivity
    apply intervalIntegral.integral_mono_on h12 (hcK.intervalIntegrable_of_Icc h12)
      (hDii s₁ s₂ hs1 h12)
    intro s hs
    have hs0 : 0 < s := hs1.trans_le hs.1
    have h1C : 0 < 1 + C * s := by positivity
    rw [div_le_iff₀ (by positivity)]
    have := hKD s hs0
    calc Kf s ≤ (C * s ^ 2 + s) / 2 * D s := this
      _ = 1 / 2 * D s * (s * (1 + C * s)) := by ring
  -- the limit `T → ∞`
  obtain ⟨Lf, hLf⟩ := be_tc_lipschitz hf
  have hlimT : Tendsto I atTop (𝓝 (∫ x, Φ (f x) ∂μ)) :=
    tendsto_Ifun_top hJ.1 hΦ2 hIcc hLf hfr
  have hlimK : Tendsto (fun T => Kf T * ((1 + C * T) / T)) atTop
      (𝓝 (PhiSobBayes.phiEnt μ Φ f * C)) := by
    have h1 : Tendsto Kf atTop (𝓝 (PhiSobBayes.phiEnt μ Φ f)) := hlimT.sub_const _
    have h2 : Tendsto (fun T : ℝ => (1 + C * T) / T) atTop (𝓝 C) := by
      have h3 : Tendsto (fun T : ℝ => T⁻¹ + C) atTop (𝓝 (0 + C)) :=
        tendsto_inv_atTop_zero.add_const C
      rw [zero_add] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      field_simp
    exact h1.mul h2
  have hfin : Kf t * ((1 + C * t) / t) ≤ PhiSobBayes.phiEnt μ Φ f * C :=
    ge_of_tendsto hlimK (by
      filter_upwards [eventually_ge_atTop t] with T hT using hmono T hT)
  rw [hKphi t ht]
  have h1C : 0 < 1 + C * t := by positivity
  have key : Kf t * (1 + C * t) ≤ PhiSobBayes.phiEnt μ Φ f * C * t := by
    have := mul_le_mul_of_nonneg_right hfin ht.le
    calc Kf t * (1 + C * t) = Kf t * ((1 + C * t) / t) * t := by field_simp
      _ ≤ _ := this
  rw [div_mul_eq_mul_div, le_div_iff₀ h1C]
  linarith


/-! ### Theorem 3.1 (forward direction), log-concave prior -/

theorem fwd_lc {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : PhiSobBayes.IsLogConcave μ)
    (C : ℝ) (hC : 0 < C) (J : Set ℝ) (hJ : PhiSobBayes.IsOpenInterval J) (Φ : ℝ → ℝ)
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ)
    (hS : PhiSobBayes.PhiSobolev μ J Φ C) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ PhiSobBayes.testClass n J)
    (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (PhiSobBayes.phiEnt μ Φ f / (1 + C * t)) ≤ PhiSobBayes.bayesRisk μ J Φ t f := by
  have hP : IsProbabilityMeasure μ := hμ.1
  obtain ⟨lo, hi, hlo, hhi, hfr⟩ := be_tc_range hf
  have hIcc : Set.Icc lo hi ⊆ J := hJ.2.1.out hlo hhi
  have hfc : Continuous f := (tc_fderiv_eq hf).choose_spec.2.2.2.continuous
  have hfm : Measurable f := hfc.measurable
  have hle : lo ≤ hi := (hfr 0).1.trans (hfr 0).2
  have hΦIcc : ContinuousOn Φ (Set.Icc lo hi) := hΦ.1.continuousOn.mono hIcc
  obtain ⟨MΦ, hMΦ⟩ := be_bdd_comp hΦIcc
  have hfint : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable (max |lo| |hi|)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [neg_abs_le lo, le_max_left |lo| |hi|, (hfr x).1]
      · linarith [le_abs_self hi, le_max_right |lo| |hi|, (hfr x).2])
  have hΦfint : Integrable (fun x => Φ (f x)) μ :=
    Integrable.of_bound (be_meas_comp hle hΦIcc hfm hfr).aestronglyMeasurable MΦ
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hMΦ _ (hfr x))
  have hconv : ConvexOn ℝ J Φ := by
    have hd1 : ContDiffOn ℝ ∞ (deriv Φ) J := hΦ.1.deriv_of_isOpen hJ.1 (by simp)
    exact convexOn_of_deriv2_nonneg' hJ.2.1.convex (hΦ.1.differentiableOn (by simp))
      (hd1.differentiableOn (by simp)) (fun z hz => by simpa using (hΦ.2.1 z hz).le)
  have h62 := PhiSobBayes.lemma_6_2 μ J hJ Φ hΦ.1 hconv f hf.2 hfint hΦfint t ht
  obtain ⟨-, hR, hdec, -⟩ := h62
  rw [hR, hdec]
  -- identify the observation-law term with `K(t)`
  set m : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ∫ x, f x ∂(PhiSobBayes.posterior μ t y)
    with hmdef
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hmθ : ∀ θ, m ((Real.sqrt t)⁻¹ • θ) = pmean μ t θ f := by
    intro θ
    simp only [hmdef]
    rw [posterior_eq_post μ t ht.le, smul_smul, mul_inv_cancel₀ hsq.ne', one_smul]
    rfl
  have hmy : ∀ y, m y = pmean μ t (Real.sqrt t • y) f := by
    intro y
    have := hmθ (Real.sqrt t • y)
    rwa [smul_smul, inv_mul_cancel₀ hsq.ne', one_smul] at this
  have hmmeas : Measurable m := by
    have : m = (fun θ => pmean μ t θ f) ∘ (fun y => Real.sqrt t • y) := by
      funext y; exact hmy y
    rw [this]
    exact (measurable_pmean ht hfm).comp (measurable_const_smul _)
  have hmr : ∀ y, m y ∈ Set.Icc lo hi := fun y => by
    rw [hmy y]; exact be_pmean_mem ht _ hfm hfr
  have hobs : PhiSobBayes.phiEnt (PhiSobBayes.gamObs μ t) Φ m =
      PhiSobBayes.phiEnt (Qt μ t) Φ (fun θ => pmean μ t θ f) := by
    unfold PhiSobBayes.phiEnt
    rw [gamObs_eq_map_Qt μ t ht]
    have hφ : AEMeasurable (fun θ : EuclideanSpace ℝ (Fin n) => (Real.sqrt t)⁻¹ • θ) (Qt μ t) :=
      (measurable_const_smul _).aemeasurable
    rw [integral_map hφ (be_meas_comp hle hΦIcc hmmeas hmr).aestronglyMeasurable,
      integral_map hφ hmmeas.aestronglyMeasurable]
    simp only [hmθ]
  rw [hobs]
  have hK := fwd_K_le hμ hC hJ hΦ hS hf ht
  apply ENNReal.ofReal_le_ofReal
  have h1C : 0 < 1 + C * t := by positivity
  rw [div_le_iff₀ h1C]
  have e : C * t / (1 + C * t) * PhiSobBayes.phiEnt μ Φ f * (1 + C * t) =
      C * t * PhiSobBayes.phiEnt μ Φ f := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hK h1C.le]

end PSBSL

end
end

-- ===== FwdSol.lean =====
section

theorem solution {n : ℕ} (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) (hμ : PhiSobBayes.IsLogConcave μ)
    (C : ℝ) (hC : 0 < C) (J : Set ℝ) (hJ : PhiSobBayes.IsOpenInterval J) (Φ : ℝ → ℝ)
    (hΦ : PhiSobBayes.AdmissiblePhi J Φ)
    (hS : PhiSobBayes.PhiSobolev μ J Φ C) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ PhiSobBayes.testClass n J)
    (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (PhiSobBayes.phiEnt μ Φ f / (1 + C * t)) ≤ PhiSobBayes.bayesRisk μ J Φ t f :=
  PSBSL.fwd_lc μ hμ C hC J hJ Φ hΦ hS f hf t ht

end
