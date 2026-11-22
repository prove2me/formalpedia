-- Prove2me | solution 1 for RobustOpt2009.MatrixChance.gaussian_smooth_approximation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T21:11:13.324371+00:00
-- url     : https://prove2.me/submissions/acd901ff-5e95-480f-b6c3-e1a3551ce320

import Theorems.Thm_OAI_GaussianPropeller_Translation_stdGaussian_map_add
import Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_fderiv_heat

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators RealInnerProductSpace NNReal ENNReal

open OAI.GaussianPropeller.HeatConvolution
open OAI.GaussianPropeller.Translation

namespace BorellSmoothing

section GaussianSmoothing

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "γ" => stdGaussian (EuclideanSpace ℝ (Fin m))

private lemma integrable_norm_stdGaussian : Integrable (fun z : E => ‖z‖) γ :=
  (IsGaussian.integrable_id (μ := γ)).norm

private lemma integrable_mul_exp_norm_stdGaussian :
    Integrable (fun z : E => (‖z‖ + 1) * Real.exp ‖z‖) γ := by
  obtain ⟨C, hC_pos, hC_int⟩ := IsGaussian.exists_integrable_exp_sq (μ := γ)
  refine (hC_int.const_mul (Real.exp (1 / C))).mono' (by fun_prop) (ae_of_all _ fun z => ?_)
  have hnn : 0 ≤ (‖z‖ + 1) * Real.exp ‖z‖ := by positivity
  rw [Real.norm_of_nonneg hnn, ← Real.exp_add]
  have h1 : ‖z‖ + 1 ≤ Real.exp ‖z‖ := Real.add_one_le_exp ‖z‖
  have h2 : (‖z‖ + 1) * Real.exp ‖z‖ ≤ Real.exp (2 * ‖z‖) := by
    calc (‖z‖ + 1) * Real.exp ‖z‖
        ≤ Real.exp ‖z‖ * Real.exp ‖z‖ := by gcongr
      _ = Real.exp (2 * ‖z‖) := by rw [← Real.exp_add]; ring_nf
  refine h2.trans (Real.exp_le_exp.mpr ?_)
  have hsq : 0 ≤ (C * ‖z‖ - 1) ^ 2 := sq_nonneg _
  have hmul : 2 * C * ‖z‖ ≤ 1 + C ^ 2 * ‖z‖ ^ 2 := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hmul hC_pos.le
  calc 2 * ‖z‖ = (2 * C * ‖z‖) / C := by field_simp [hC_pos.ne']
    _ ≤ (1 + C ^ 2 * ‖z‖ ^ 2) / C := hdiv
    _ = 1 / C + C * ‖z‖ ^ 2 := by field_simp [hC_pos.ne']

private lemma norm_smulRight_le {E' V : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E' →L[ℝ] ℝ) (v : V) :
    ‖L.smulRight v‖ ≤ ‖L‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, Real.norm_eq_abs]
  calc |L x| * ‖v‖ ≤ (‖L‖ * ‖x‖) * ‖v‖ := by gcongr; exact ContinuousLinearMap.le_opNorm L x
    _ = ‖L‖ * ‖v‖ * ‖x‖ := by ring

private lemma hasFDerivAt_congr_deriv {E' V : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : E' → V} {L₁ L₂ : E' →L[ℝ] V} {x : E'}
    (h : HasFDerivAt f L₁ x) (heq : L₁ = L₂) : HasFDerivAt f L₂ x :=
  heq ▸ h

private lemma continuous_shift_scale (x : E) (r : ℝ) : Continuous (fun z : E => x + r • z) :=
  continuous_const.add (continuous_id.const_smul r)

private lemma integrable_heat_integrand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E → V} (hFc : Continuous F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (t : ℝ) (x : E) :
    Integrable (fun z : E => F (x + Real.sqrt t • z)) γ :=
  Integrable.of_bound (hFc.comp (continuous_shift_scale x (Real.sqrt t))).aestronglyMeasurable
    B (ae_of_all _ fun _ => hB _)

private lemma heat_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : E → V) (x : E) : heat F 0 x = F x := by
  simp [heat]

private lemma heat_one_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) : heat F 1 0 = ∫ z, F z ∂γ := by
  simp [heat]

private lemma norm_heat_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E → V} {B : ℝ} (_hB0 : 0 ≤ B) (hB : ∀ x, ‖F x‖ ≤ B) (t : ℝ) (x : E) :
    ‖heat F t x‖ ≤ B := by
  unfold heat
  calc ‖∫ z, F (x + Real.sqrt t • z) ∂γ‖
      ≤ ∫ z, ‖F (x + Real.sqrt t • z)‖ ∂γ := norm_integral_le_integral_norm _
    _ ≤ ∫ _z, B ∂γ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          (integrable_const B) (ae_of_all _ fun z => hB _)
    _ = B := by simp

private lemma continuous_heat {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E → V} (hFc : Continuous F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Continuous (fun p : ℝ × E => heat F p.1 p.2) := by
  refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · intro p
    exact (hFc.comp (continuous_shift_scale p.2 (Real.sqrt p.1))).aestronglyMeasurable
  · intro p
    exact ae_of_all _ fun z => hB _
  · exact ae_of_all _ fun z => hFc.comp (continuous_snd.add
      ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))

private lemma heat_mem_Icc {F : E → ℝ} {lo hi : ℝ} (hFc : Continuous F)
    (hF : ∀ x, F x ∈ Icc lo hi) (t : ℝ) (x : E) : heat F t x ∈ Icc lo hi := by
  have hbound : ∀ u, ‖F u‖ ≤ max |lo| |hi| := fun u => by
    rw [Real.norm_eq_abs, abs_le]
    have h := hF u
    exact ⟨le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le _) h.1),
      le_trans h.2 (le_trans (le_abs_self _) (le_max_right _ _))⟩
  have hint : Integrable (fun z => F (x + Real.sqrt t • z)) γ :=
    integrable_heat_integrand hFc hbound t x
  unfold heat
  constructor
  · calc lo = ∫ _z, lo ∂γ := by simp
      _ ≤ ∫ z, F (x + Real.sqrt t • z) ∂γ :=
          integral_mono (integrable_const _) hint fun z => (hF _).1
  · calc ∫ z, F (x + Real.sqrt t • z) ∂γ
        ≤ ∫ _z, hi ∂γ := integral_mono hint (integrable_const _) fun z => (hF _).2
      _ = hi := by simp

private lemma heat_lipschitz_one {F : E → ℝ} (hFc : Continuous F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B)
    (hLip : ∀ x y, |F x - F y| ≤ ‖x - y‖) (t : ℝ) (x y : E) :
    |heat F t x - heat F t y| ≤ ‖x - y‖ := by
  have hint : ∀ u : E, Integrable (fun z => F (u + Real.sqrt t • z)) γ := fun u =>
    integrable_heat_integrand hFc hB t u
  unfold heat
  rw [← integral_sub (hint x) (hint y)]
  calc |∫ z, (F (x + Real.sqrt t • z) - F (y + Real.sqrt t • z)) ∂γ|
      ≤ ∫ z, |F (x + Real.sqrt t • z) - F (y + Real.sqrt t • z)| ∂γ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun z => F (x + Real.sqrt t • z) - F (y + Real.sqrt t • z))
    _ ≤ ∫ _z, ‖x - y‖ ∂γ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (integrable_const _) (ae_of_all _ fun z => ?_)
        simpa [add_sub_add_right_eq_sub] using hLip (x + Real.sqrt t • z) (y + Real.sqrt t • z)
    _ = ‖x - y‖ := by simp

private lemma heat_sub_self_le {F : E → ℝ} (hFc : Continuous F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B)
    (hLip : ∀ x y, |F x - F y| ≤ ‖x - y‖) {a : ℝ} (_ha : 0 ≤ a) (x : E) :
    |heat F a x - F x| ≤ Real.sqrt a * ∫ z, ‖z‖ ∂γ := by
  have hint : Integrable (fun z => F (x + Real.sqrt a • z)) γ :=
    integrable_heat_integrand hFc hB a x
  unfold heat
  have hconst : F x = ∫ _z, F x ∂γ := by simp
  conv_lhs => rw [hconst]
  rw [← integral_sub hint (integrable_const _)]
  calc |∫ z, (F (x + Real.sqrt a • z) - F x) ∂γ|
      ≤ ∫ z, |F (x + Real.sqrt a • z) - F x| ∂γ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun z => F (x + Real.sqrt a • z) - F x)
    _ ≤ ∫ z, Real.sqrt a * ‖z‖ ∂γ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (integrable_norm_stdGaussian.const_mul _) (ae_of_all _ fun z => ?_)
        have h := hLip (x + Real.sqrt a • z) x
        simpa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg a)] using h
    _ = Real.sqrt a * ∫ z, ‖z‖ ∂γ := integral_const_mul _ _

/-- Change-of-variables formula for `heat F a (x + h)` using Cameron–Martin shift. -/
private lemma heat_add_eq_cameronMartin {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E → V} (hFc : Continuous F) {a : ℝ} (ha : 0 < a) (x h : E) :
    heat F a (x + h) =
      ∫ y, Real.exp ((Real.sqrt a)⁻¹ * ⟪h, y⟫ - ‖h‖ ^ 2 / (2 * a)) •
        F (x + Real.sqrt a • y) ∂γ := by
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set w : E := (Real.sqrt a)⁻¹ • h
  have hshift : ∀ z : E, x + h + Real.sqrt a • z = x + Real.sqrt a • (z + w) := fun z => by
    simp only [w, smul_add, smul_smul, mul_inv_cancel₀ hsq.ne', one_smul]
    abel
  unfold heat
  simp_rw [hshift]
  have hmap : (∫ z, F (x + Real.sqrt a • (z + w)) ∂γ) =
      ∫ y, F (x + Real.sqrt a • y) ∂(Measure.map (fun z => z + w) γ) := by
    rw [integral_map (measurable_add_const w).aemeasurable]
    exact (hFc.comp (continuous_shift_scale x (Real.sqrt a))).aestronglyMeasurable
  rw [hmap, stdGaussian_map_add w]
  have hd_meas : Measurable (fun y : E => ENNReal.ofReal (Real.exp (⟪w, y⟫ - ‖w‖ ^ 2 / 2))) := by
    fun_prop
  have hd_lt : ∀ᵐ y ∂γ, ENNReal.ofReal (Real.exp (⟪w, y⟫ - ‖w‖ ^ 2 / 2)) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hd_meas hd_lt]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  congr 2
  have h1 : ⟪w, y⟫ = (Real.sqrt a)⁻¹ * ⟪h, y⟫ := by
    simp [w, real_inner_smul_left]
  have h2 : ‖w‖ ^ 2 / 2 = ‖h‖ ^ 2 / (2 * a) := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsq), mul_pow, inv_pow,
      Real.sq_sqrt ha.le]
    ring
  rw [h1, h2]

/-- One-step Gaussian smoothing: for any continuous bounded `F : E → V` and `a > 0`,
`heat F a` is globally `C¹_b` with continuous bounded Fréchet derivative. -/
private lemma heat_smooth_step {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {F : E → V} (hFc : Continuous F) {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ x, ‖F x‖ ≤ B) {a : ℝ} (ha : 0 < a) :
    ∃ L : E → (E →L[ℝ] V),
      (∀ x, HasFDerivAt (heat F a) (L x) x) ∧
      Continuous L ∧
      (∀ x, ‖L x‖ ≤ (Real.sqrt a)⁻¹ * B * ∫ z, ‖z‖ ∂γ) := by
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  let L : E → (E →L[ℝ] V) := fun x =>
    (Real.sqrt a)⁻¹ • ∫ y, (innerSL ℝ y).smulRight (F (x + Real.sqrt a • y)) ∂γ
  refine ⟨L, ?_, ?_, ?_⟩
  · intro x
    let G : E → E → V := fun h y =>
      Real.exp ((Real.sqrt a)⁻¹ * ⟪h, y⟫ - ‖h‖ ^ 2 / (2 * a)) • F (x + Real.sqrt a • y)
    let G' : E → E → (E →L[ℝ] V) := fun h y =>
      (Real.exp ((Real.sqrt a)⁻¹ * ⟪h, y⟫ - ‖h‖ ^ 2 / (2 * a)) •
        ((Real.sqrt a)⁻¹ • innerSL ℝ y - a⁻¹ • innerSL ℝ h)).smulRight (F (x + Real.sqrt a • y))
    have hdiff : ∀ y : E, ∀ h : E, HasFDerivAt (G · y) (G' h y) h := fun y h => by
      have h1 : HasFDerivAt (fun u : E => (Real.sqrt a)⁻¹ * ⟪u, y⟫)
          ((Real.sqrt a)⁻¹ • innerSL ℝ y) h := by
        have hlin : (fun u : E => (Real.sqrt a)⁻¹ * ⟪u, y⟫) =
            fun u => (Real.sqrt a)⁻¹ * innerSL ℝ y u := by
          ext u; simp [real_inner_comm]
        rw [hlin]
        exact ((innerSL ℝ y).hasFDerivAt).const_mul (Real.sqrt a)⁻¹
      have h2 : HasFDerivAt (fun u : E => ‖u‖ ^ 2 / (2 * a)) (a⁻¹ • innerSL ℝ h) h := by
        have hinner : HasFDerivAt (fun u : E => ⟪u, u⟫) ((2 : ℝ) • innerSL ℝ h) h := by
          have hi := (hasFDerivAt_id h).inner ℝ (hasFDerivAt_id h)
          have heq : fderivInnerCLM ℝ (h, h) ∘L
              ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) =
              (2 : ℝ) • innerSL ℝ h := by
            ext v
            simp [real_inner_comm, two_mul]
          rw [← heq]
          exact hi
        have hsq' : (fun u : E => ‖u‖ ^ 2 / (2 * a)) = fun u => (2 * a)⁻¹ * ⟪u, u⟫ := by
          ext u; rw [real_inner_self_eq_norm_sq]; ring
        rw [hsq']
        have hd := hinner.const_mul (2 * a)⁻¹
        refine hasFDerivAt_congr_deriv hd ?_
        ext v
        simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
        field_simp [ha.ne']
      have hexp := (Real.hasDerivAt_exp _).comp_hasFDerivAt h (h1.sub h2)
      exact hexp.smul_const (F (x + Real.sqrt a • y))
    have hbound : ∀ y : E, ∀ h ∈ Metric.ball (0 : E) (Real.sqrt a),
        ‖G' h y‖ ≤ (Real.sqrt a)⁻¹ * B * ((‖y‖ + 1) * Real.exp ‖y‖) := by
      intro y h hh
      rw [Metric.mem_ball, dist_zero_right] at hh
      have hexp_le : Real.exp ((Real.sqrt a)⁻¹ * ⟪h, y⟫ - ‖h‖ ^ 2 / (2 * a)) ≤ Real.exp ‖y‖ := by
        apply Real.exp_le_exp.mpr
        have hcs : ⟪h, y⟫ ≤ ‖h‖ * ‖y‖ := real_inner_le_norm h y
        have hnn : 0 ≤ ‖h‖ ^ 2 / (2 * a) := by positivity
        have h1 : (Real.sqrt a)⁻¹ * ⟪h, y⟫ ≤ (Real.sqrt a)⁻¹ * (‖h‖ * ‖y‖) := by gcongr
        have h2 : (Real.sqrt a)⁻¹ * (‖h‖ * ‖y‖) ≤ ‖y‖ := by
          calc (Real.sqrt a)⁻¹ * (‖h‖ * ‖y‖)
              ≤ (Real.sqrt a)⁻¹ * (Real.sqrt a * ‖y‖) := by gcongr
            _ = ‖y‖ := by field_simp [hsq.ne']
        linarith
      have hlin_le : ‖(Real.sqrt a)⁻¹ • innerSL ℝ y - a⁻¹ • innerSL ℝ h‖ ≤
          (Real.sqrt a)⁻¹ * (‖y‖ + 1) := by
        calc ‖(Real.sqrt a)⁻¹ • innerSL ℝ y - a⁻¹ • innerSL ℝ h‖
            ≤ ‖(Real.sqrt a)⁻¹ • innerSL ℝ y‖ + ‖a⁻¹ • innerSL ℝ h‖ := norm_sub_le _ _
          _ = (Real.sqrt a)⁻¹ * ‖innerSL ℝ y‖ + a⁻¹ * ‖innerSL ℝ h‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsq.le),
                Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
          _ ≤ (Real.sqrt a)⁻¹ * ‖y‖ + a⁻¹ * ‖h‖ := by
              gcongr
              · exact (innerSL_apply_norm ℝ y).le
              · exact (innerSL_apply_norm ℝ h).le
          _ ≤ (Real.sqrt a)⁻¹ * ‖y‖ + a⁻¹ * Real.sqrt a := by gcongr
          _ = (Real.sqrt a)⁻¹ * (‖y‖ + 1) := by
              have hinv : a⁻¹ * Real.sqrt a = (Real.sqrt a)⁻¹ := by
                calc a⁻¹ * Real.sqrt a
                    = (Real.sqrt a * Real.sqrt a)⁻¹ * Real.sqrt a := by rw [Real.mul_self_sqrt ha.le]
                  _ = (Real.sqrt a)⁻¹ := by field_simp [hsq.ne']
              rw [hinv]; ring
      calc ‖G' h y‖
          ≤ ‖Real.exp ((Real.sqrt a)⁻¹ * ⟪h, y⟫ - ‖h‖ ^ 2 / (2 * a)) •
              ((Real.sqrt a)⁻¹ • innerSL ℝ y - a⁻¹ • innerSL ℝ h)‖ *
              ‖F (x + Real.sqrt a • y)‖ := norm_smulRight_le _ _
        _ = Real.exp ((Real.sqrt a)⁻¹ * ⟪h, y⟫ - ‖h‖ ^ 2 / (2 * a)) *
              ‖(Real.sqrt a)⁻¹ • innerSL ℝ y - a⁻¹ • innerSL ℝ h‖ *
              ‖F (x + Real.sqrt a • y)‖ := by
              rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
        _ ≤ Real.exp ‖y‖ * ((Real.sqrt a)⁻¹ * (‖y‖ + 1)) * B := by
              gcongr
              exact hB _
        _ = (Real.sqrt a)⁻¹ * B * ((‖y‖ + 1) * Real.exp ‖y‖) := by ring
    have hF_meas : ∀ᶠ h in 𝓝 (0 : E), AEStronglyMeasurable (G h) γ :=
      Filter.Eventually.of_forall fun h =>
        (Continuous.aestronglyMeasurable (by fun_prop))
    have hF_int : Integrable (G 0) γ := by
      have h0 : G 0 = fun y => F (x + Real.sqrt a • y) := by
        ext y; simp [G]
      rw [h0]
      exact integrable_heat_integrand hFc hB a x
    have hF'_meas : AEStronglyMeasurable (G' 0) γ := by
      have h0 : G' 0 = fun y =>
          ((Real.sqrt a)⁻¹ • innerSL ℝ y).smulRight (F (x + Real.sqrt a • y)) := by
        ext y v; simp [G']
      rw [h0]
      exact (Continuous.aestronglyMeasurable <| by
        have h1 : Continuous (fun y : E => (Real.sqrt a)⁻¹ • innerSL ℝ y) :=
          ((InnerProductSpace.toDual ℝ E).continuous).const_smul (Real.sqrt a)⁻¹
        have h2 : Continuous (fun y : E => F (x + Real.sqrt a • y)) :=
          hFc.comp (continuous_shift_scale x (Real.sqrt a))
        exact ((ContinuousLinearMap.smulRightL ℝ E V).continuous.comp h1).clm_apply h2)
    have hres := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds (0 : E) hsq) hF_meas hF_int hF'_meas
      (ae_of_all _ hbound) (integrable_mul_exp_norm_stdGaussian.const_mul _)
      (ae_of_all _ fun y h _ => hdiff y h)
    have hEq : (fun h => ∫ y, G h y ∂γ) = (fun h => heat F a (x + h)) := by
      ext h
      exact (heat_add_eq_cameronMartin hFc ha x h).symm
    have hL_eq : ∫ y, G' 0 y ∂γ = L x := by
      have hG0 : G' 0 = fun y =>
          (Real.sqrt a)⁻¹ • (innerSL ℝ y).smulRight (F (x + Real.sqrt a • y)) := by
        ext y v; simp [G', smul_smul]
      rw [hG0, integral_smul]
    rw [hEq, hL_eq] at hres
    have hsub : HasFDerivAt (fun y : E => y - x) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).sub_const x
    have hres' : HasFDerivAt (fun h => heat F a (x + h)) (L x) ((fun y => y - x) x) := by
      simpa using hres
    have hcomp := HasFDerivAt.comp x (f := fun y => y - x) hres' hsub
    have hfun : (fun h => heat F a (x + h)) ∘ (fun y => y - x) = heat F a := by
      ext y; simp
    rw [hfun] at hcomp
    simpa using hcomp
  · -- Continuity of L
    have hcont_int : Continuous (fun x : E =>
        ∫ y, (innerSL ℝ y).smulRight (F (x + Real.sqrt a • y)) ∂γ) := by
      refine continuous_of_dominated (bound := fun y => B * ‖y‖) ?_ ?_
        (integrable_norm_stdGaussian.const_mul B) ?_
      · intro x
        have h1 : Continuous (fun y : E => innerSL ℝ y) :=
          (InnerProductSpace.toDual ℝ E).continuous
        have h2 : Continuous (fun y : E => F (x + Real.sqrt a • y)) :=
          hFc.comp (continuous_shift_scale x (Real.sqrt a))
        exact (((ContinuousLinearMap.smulRightL ℝ E V).continuous.comp h1).clm_apply h2).aestronglyMeasurable
      · intro x
        refine ae_of_all _ fun y => ?_
        calc ‖(innerSL ℝ y).smulRight (F (x + Real.sqrt a • y))‖
            ≤ ‖innerSL ℝ y‖ * ‖F (x + Real.sqrt a • y)‖ := norm_smulRight_le _ _
          _ ≤ ‖y‖ * B := by
              gcongr
              · exact (innerSL_apply_norm ℝ y).le
              · exact hB _
          _ = B * ‖y‖ := mul_comm _ _
      · refine ae_of_all _ fun y => ?_
        have h2 : Continuous (fun x : E => F (x + Real.sqrt a • y)) :=
          hFc.comp (continuous_id.add continuous_const)
        exact (ContinuousLinearMap.smulRightL ℝ E V (innerSL ℝ y)).continuous.comp h2
    exact hcont_int.const_smul (Real.sqrt a)⁻¹
  · -- Norm bound on L
    intro x
    dsimp only [L]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsq.le)]
    calc (Real.sqrt a)⁻¹ * ‖∫ y, (innerSL ℝ y).smulRight (F (x + Real.sqrt a • y)) ∂γ‖
        ≤ (Real.sqrt a)⁻¹ * ∫ y, ‖(innerSL ℝ y).smulRight (F (x + Real.sqrt a • y))‖ ∂γ := by
          gcongr
          exact norm_integral_le_integral_norm _
      _ ≤ (Real.sqrt a)⁻¹ * ∫ y, B * ‖y‖ ∂γ := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hsq.le)
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
            (integrable_norm_stdGaussian.const_mul B) (ae_of_all _ fun y => ?_)
          calc ‖(innerSL ℝ y).smulRight (F (x + Real.sqrt a • y))‖
              ≤ ‖innerSL ℝ y‖ * ‖F (x + Real.sqrt a • y)‖ := norm_smulRight_le _ _
            _ ≤ ‖y‖ * B := by
                gcongr
                · exact (innerSL_apply_norm ℝ y).le
                · exact hB _
            _ = B * ‖y‖ := mul_comm _ _
      _ = (Real.sqrt a)⁻¹ * B * ∫ y, ‖y‖ ∂γ := by
          rw [integral_const_mul]; ring

private lemma heat_clm_eval {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {F : E → (E →L[ℝ] V)} (hFc : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) (v : E) (t : ℝ) (x : E) :
    heat F t x v = heat (fun y => F y v) t x := by
  unfold heat
  exact ((ContinuousLinearMap.apply ℝ V v).integral_comp_comm
    (integrable_heat_integrand hFc hB t x)).symm

private lemma continuous_clm_add_sub_sub {α E' W : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {a b c d : α → (E' →L[ℝ] W)}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun x => (a x + b x) - c x - d x) :=
  ((ha.add hb).sub hc).sub hd

private lemma norm_smul_clm {E' W : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup W] [NormedSpace ℝ W] (c : ℝ) (T : E' →L[ℝ] W) :
    ‖c • T‖ = |c| * ‖T‖ := by
  rw [norm_smul, Real.norm_eq_abs]

private lemma norm_clm_add_sub_sub_le {E' W : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup W] [NormedSpace ℝ W] (a b c d : E' →L[ℝ] W) :
    ‖(a + b) - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc ‖(a + b) - c - d‖ ≤ ‖(a + b) - c‖ + ‖d‖ := norm_sub_le _ _
    _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _

private lemma heat_innerSL_eq {g : E → E} (hgc : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (t : ℝ) (x : E) :
    heat (fun y => innerSL ℝ (g y)) t x = innerSL ℝ (heat g t x) := by
  unfold heat
  have hint : Integrable (fun z => g (x + Real.sqrt t • z)) γ :=
    integrable_heat_integrand hgc hB t x
  exact (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.integral_comp_comm hint

/-- 3-step smooth approximation of any continuous bounded 1-Lipschitz function `d : E → [0, R]`. -/
private lemma exists_C3_approx {d : E → ℝ} (hdc : Continuous d) {R : ℝ} (hR : 0 ≤ R)
    (hd_mem : ∀ x, d x ∈ Icc 0 R) (hd_lip : ∀ x y, |d x - d y| ≤ ‖x - y‖)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : E → ℝ) (g : E → E) (K : E → (E →L[ℝ] E)) (M : E → (E →L[ℝ] (E →L[ℝ] E)))
      (CK CM : ℝ),
      (∀ x, F x ∈ Icc 0 R) ∧
      (∀ x, |F x - d x| ≤ δ) ∧
      (∀ x, HasFDerivAt F (innerSL ℝ (g x)) x) ∧
      (∀ x, HasFDerivAt g (K x) x) ∧
      (∀ x, HasFDerivAt K (M x) x) ∧
      Continuous M ∧
      (∀ x v w, ⟪K x v, w⟫ = ⟪v, K x w⟫) ∧
      (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖K x‖ ≤ CK) ∧
      (∀ x, ‖M x‖ ≤ CM) := by
  set I1 : ℝ := ∫ z, ‖z‖ ∂γ
  have hI1_nn : 0 ≤ I1 := integral_nonneg fun _ => norm_nonneg _
  set a : ℝ := (δ / (3 * (I1 + 1))) ^ 2
  have ha_pos : 0 < a := by positivity
  have ha_sqrt : Real.sqrt a = δ / (3 * (I1 + 1)) := by
    rw [Real.sqrt_sq (by positivity)]
  have hstep_err : Real.sqrt a * I1 ≤ δ / 3 := by
    rw [ha_sqrt]
    have h1 : I1 ≤ I1 + 1 := by linarith
    calc δ / (3 * (I1 + 1)) * I1 ≤ δ / (3 * (I1 + 1)) * (I1 + 1) := by gcongr
      _ = δ / 3 := by field_simp [(by positivity : (0 : ℝ) < I1 + 1).ne']
  have hd_bound : ∀ x, ‖d x‖ ≤ R := fun x => by
    rw [Real.norm_of_nonneg (hd_mem x).1]; exact (hd_mem x).2
  -- Step 1: F₁ = heat d a
  let F₁ : E → ℝ := heat d a
  have hF₁_mem : ∀ x, F₁ x ∈ Icc 0 R := fun x => heat_mem_Icc hdc hd_mem a x
  have hF₁_bound : ∀ x, ‖F₁ x‖ ≤ R := fun x => by
    rw [Real.norm_of_nonneg (hF₁_mem x).1]; exact (hF₁_mem x).2
  have hF₁_lip : ∀ x y, |F₁ x - F₁ y| ≤ ‖x - y‖ := heat_lipschitz_one hdc hd_bound hd_lip a
  obtain ⟨DF₁, hDF₁_deriv, hDF₁_cont, hDF₁_bound⟩ := heat_smooth_step hdc hR hd_bound ha_pos
  let g₁ : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (DF₁ x)
  have hg₁_eq : ∀ x, innerSL ℝ (g₁ x) = DF₁ x := fun x =>
    (InnerProductSpace.toDual ℝ E).apply_symm_apply (DF₁ x)
  have hF₁_deriv : ∀ x, HasFDerivAt F₁ (innerSL ℝ (g₁ x)) x := fun x => by
    rw [hg₁_eq]; exact hDF₁_deriv x
  have hg₁_cont : Continuous g₁ := (InnerProductSpace.toDual ℝ E).symm.continuous.comp hDF₁_cont
  set B₁ : ℝ := (Real.sqrt a)⁻¹ * R * I1
  have hB₁_nn : 0 ≤ B₁ := by positivity
  have hg₁_bound : ∀ x, ‖g₁ x‖ ≤ B₁ := fun x => by
    rw [show ‖g₁ x‖ = ‖DF₁ x‖ from (InnerProductSpace.toDual ℝ E).symm.norm_map (DF₁ x)]
    exact hDF₁_bound x
  have hF₁_cont : Continuous F₁ := continuous_iff_continuousAt.mpr fun x =>
    (hF₁_deriv x).continuousAt
  -- Step 2: F₂ = heat F₁ a, g₂ = heat g₁ a
  let F₂ : E → ℝ := heat F₁ a
  let g₂ : E → E := heat g₁ a
  have hF₂_mem : ∀ x, F₂ x ∈ Icc 0 R := fun x => heat_mem_Icc hF₁_cont hF₁_mem a x
  have hF₂_bound : ∀ x, ‖F₂ x‖ ≤ R := fun x => by
    rw [Real.norm_of_nonneg (hF₂_mem x).1]; exact (hF₂_mem x).2
  have hF₂_lip : ∀ x y, |F₂ x - F₂ y| ≤ ‖x - y‖ := heat_lipschitz_one hF₁_cont hF₁_bound hF₁_lip a
  have hF₂_deriv : ∀ x, HasFDerivAt F₂ (innerSL ℝ (g₂ x)) x := fun x => by
    have h := fderiv_heat (F := F₁) (D := fun y => innerSL ℝ (g₁ y))
      hF₁_deriv ((InnerProductSpace.toDual ℝ E).continuous.comp hg₁_cont)
      hF₁_bound (fun y => by rw [hg₁_eq]; exact hDF₁_bound y) a x
    rwa [heat_innerSL_eq hg₁_cont hg₁_bound a x] at h
  have hF₂_cont : Continuous F₂ := continuous_iff_continuousAt.mpr fun x =>
    (hF₂_deriv x).continuousAt
  obtain ⟨K₂, hK₂_deriv, hK₂_cont, hK₂_bound⟩ := heat_smooth_step hg₁_cont hB₁_nn hg₁_bound ha_pos
  set B₂ : ℝ := (Real.sqrt a)⁻¹ * B₁ * I1
  have hB₂_nn : 0 ≤ B₂ := by positivity
  have hg₂_bound : ∀ x, ‖g₂ x‖ ≤ B₁ := fun x => norm_heat_le hB₁_nn hg₁_bound a x
  have hg₂_cont : Continuous g₂ := continuous_iff_continuousAt.mpr fun x =>
    (hK₂_deriv x).continuousAt
  -- Step 3: F₃ = heat F₂ a, g₃ = heat g₂ a, K₃ = heat K₂ a
  let F₃ : E → ℝ := heat F₂ a
  let g₃ : E → E := heat g₂ a
  let K₃ : E → (E →L[ℝ] E) := heat K₂ a
  have hF₃_mem : ∀ x, F₃ x ∈ Icc 0 R := fun x => heat_mem_Icc hF₂_cont hF₂_mem a x
  have hF₃_lip : ∀ x y, |F₃ x - F₃ y| ≤ ‖x - y‖ := heat_lipschitz_one hF₂_cont hF₂_bound hF₂_lip a
  have hF₃_deriv : ∀ x, HasFDerivAt F₃ (innerSL ℝ (g₃ x)) x := fun x => by
    have h := fderiv_heat (F := F₂) (D := fun y => innerSL ℝ (g₂ y))
      hF₂_deriv ((InnerProductSpace.toDual ℝ E).continuous.comp hg₂_cont)
      hF₂_bound (fun y => by simpa [innerSL_apply_norm] using hg₂_bound y) a x
    rwa [heat_innerSL_eq hg₂_cont hg₂_bound a x] at h
  have hg₃_deriv : ∀ x, HasFDerivAt g₃ (K₃ x) x := fun x =>
    fderiv_heat hK₂_deriv hK₂_cont hg₂_bound hK₂_bound a x
  obtain ⟨M₃, hM₃_deriv, hM₃_cont, hM₃_bound⟩ := heat_smooth_step hK₂_cont hB₂_nn hK₂_bound ha_pos
  have hK₃_bound : ∀ x, ‖K₃ x‖ ≤ B₂ := fun x => norm_heat_le hB₂_nn hK₂_bound a x
  -- Error bound |F₃ x - d x| ≤ δ
  have herr : ∀ x, |F₃ x - d x| ≤ δ := fun x => by
    have e1 := heat_sub_self_le hdc hd_bound hd_lip ha_pos.le x
    have e2 := heat_sub_self_le hF₁_cont hF₁_bound hF₁_lip ha_pos.le x
    have e3 := heat_sub_self_le hF₂_cont hF₂_bound hF₂_lip ha_pos.le x
    have htri : |F₃ x - d x| ≤ |F₃ x - F₂ x| + |F₂ x - F₁ x| + |F₁ x - d x| := by
      calc |F₃ x - d x| = |(F₃ x - F₂ x) + (F₂ x - F₁ x) + (F₁ x - d x)| := by ring_nf
        _ ≤ |(F₃ x - F₂ x) + (F₂ x - F₁ x)| + |F₁ x - d x| := abs_add_le _ _
        _ ≤ |F₃ x - F₂ x| + |F₂ x - F₁ x| + |F₁ x - d x| := by gcongr; exact abs_add_le _ _
    linarith
  -- Symmetry of K₃ x via Schwarz's theorem (`second_derivative_symmetric`)
  have hK₃_symm : ∀ x v w, ⟪K₃ x v, w⟫ = ⟪v, K₃ x w⟫ := fun x v w => by
    have hDF₃ : HasFDerivAt (fun y => innerSL ℝ (g₃ y))
        ((InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp (K₃ x)) x :=
      (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp x (hg₃_deriv x)
    have hsym := second_derivative_symmetric (𝕜 := ℝ) hF₃_deriv hDF₃ v w
    simpa [real_inner_comm] using hsym
  -- Gradient norm bound ‖g₃ x‖ ≤ 1 from 1-Lipschitzness of F₃
  have hg₃_norm : ∀ x, ‖g₃ x‖ ≤ 1 := fun x => by
    by_cases h0 : g₃ x = 0
    · simp [h0]
    have hpos : 0 < ‖g₃ x‖ := norm_pos_iff.mpr h0
    have hcurve : HasDerivAt (fun t : ℝ => F₃ (x + t • g₃ x)) (‖g₃ x‖ ^ 2) 0 := by
      have hd : HasDerivAt (fun t : ℝ => x + t • g₃ x) (g₃ x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (g₃ x)).const_add x
      have hF₃0 : HasFDerivAt F₃ (innerSL ℝ (g₃ x)) (x + (0 : ℝ) • g₃ x) := by
        simpa using hF₃_deriv x
      have hc := hF₃0.comp_hasDerivAt 0 hd
      refine hc.congr_deriv ?_
      simp
    have htend := hcurve.tendsto_slope_zero_right
    have hle : ‖g₃ x‖ ^ 2 ≤ ‖g₃ x‖ := by
      refine le_of_tendsto htend ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
      calc t⁻¹ * (F₃ (x + t • g₃ x) - F₃ x)
          ≤ t⁻¹ * |F₃ (x + t • g₃ x) - F₃ x| := by gcongr; exact le_abs_self _
        _ ≤ t⁻¹ * ‖(x + t • g₃ x) - x‖ := by gcongr; exact hF₃_lip _ _
        _ = ‖g₃ x‖ := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
            field_simp [ht.ne']
    nlinarith
  exact ⟨F₃, g₃, K₃, M₃, B₂, (Real.sqrt a)⁻¹ * B₂ * I1,
    hF₃_mem, herr, hF₃_deriv, hg₃_deriv, hM₃_deriv, hM₃_cont, hK₃_symm,
    hg₃_norm, hK₃_bound, hM₃_bound⟩

end GaussianSmoothing

end BorellSmoothing

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem solution {d : E → ℝ} (hdc : Continuous d) {R : ℝ} (hR : 0 ≤ R)
    (hd_mem : ∀ x, d x ∈ Icc 0 R) (hd_lip : ∀ x y, |d x - d y| ≤ ‖x - y‖)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : E → ℝ) (g : E → E) (K : E → (E →L[ℝ] E)) (M : E → (E →L[ℝ] (E →L[ℝ] E)))
      (CK CM : ℝ),
      (∀ x, F x ∈ Icc 0 R) ∧
      (∀ x, |F x - d x| ≤ δ) ∧
      (∀ x, HasFDerivAt F (innerSL ℝ (g x)) x) ∧
      (∀ x, HasFDerivAt g (K x) x) ∧
      (∀ x, HasFDerivAt K (M x) x) ∧
      Continuous M ∧
      (∀ x v w, ⟪K x v, w⟫ = ⟪v, K x w⟫) ∧
      (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖K x‖ ≤ CK) ∧
      (∀ x, ‖M x‖ ≤ CM) :=
  BorellSmoothing.exists_C3_approx hdc hR hd_mem hd_lip hδ
