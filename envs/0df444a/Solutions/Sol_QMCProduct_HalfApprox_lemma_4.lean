-- Prove2me | solution 1 for QMCProduct.HalfApprox.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:30:29.650634+00:00
-- url     : https://prove2.me/submissions/a2f30922-01c0-4759-98ea-15af1b56c282

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open QMCProduct.HalfApprox
open scoped BigOperators NNReal ENNReal Nat

namespace Lemma4Aux

/-! ### Section 1: Characteristic-function reduction to i.i.d. bivariate Gaussians -/

noncomputable def stdGauss : Measure ℝ := gaussianReal 0 1
noncomputable def stdGauss2 : Measure (ℝ × ℝ) := stdGauss.prod stdGauss
noncomputable def stdGaussK (k : ℕ) : Measure (Fin k → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin k => stdGauss2)

instance : IsProbabilityMeasure stdGauss := by
  unfold stdGauss; infer_instance

instance : IsProbabilityMeasure stdGauss2 := by
  unfold stdGauss2; infer_instance

instance (k : ℕ) : IsProbabilityMeasure (stdGaussK k) := by
  unfold stdGaussK; infer_instance

private lemma charFunDual_real_gaussianReal (L : StrongDual ℝ ℝ) :
    charFunDual stdGauss L = Complex.exp (-((L 1 : ℂ) ^ 2 / 2)) := by
  rw [charFunDual_apply]
  have hL : ∀ x : ℝ, L x = L 1 * x := fun x => by
    have := L.map_smul x (1 : ℝ)
    simpa [smul_eq_mul, mul_comm] using this
  have h1 : (∫ x, Complex.exp ((L x : ℂ) * Complex.I) ∂stdGauss) =
      charFun stdGauss (L 1) := by
    rw [charFun_apply_real]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [hL x]
    push_cast
    ring_nf
  rw [h1, stdGauss, charFun_gaussianReal]
  simp

private lemma charFunDual_map_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) (T : E →L[ℝ] F) (L : StrongDual ℝ F) :
    charFunDual (μ.map T) L = charFunDual μ (L.comp T) := by
  rw [charFunDual_apply, charFunDual_apply, integral_map T.continuous.measurable.aemeasurable]
  · rfl
  · exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp L.continuous).mul
      continuous_const)).aestronglyMeasurable

private lemma law_proj_eq {k d : ℕ}
    (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Fin k → Fin d → Ω → ℝ) (hR : IsStdGaussianMatrix P R) :
    let t := inner ℝ u v
    let s := Real.sqrt (1 - t ^ 2)
    P.map (fun ω (a : Fin k) => (∑ c : Fin d, R a c ω * u c, ∑ c : Fin d, R a c ω * v c)) =
      (stdGaussK k).map (fun (w : Fin k → ℝ × ℝ) (a : Fin k) =>
        ((w a).1, t * (w a).1 + s * (w a).2)) := by
  intro t s
  have ht_le : t ^ 2 ≤ 1 := by
    have habs : |t| ≤ 1 := by
      simpa [t, hu, hv] using abs_real_inner_le_norm u v
    nlinarith [abs_le.mp habs]
  have hts : t ^ 2 + s ^ 2 = 1 := by
    dsimp only [s]
    rw [Real.sq_sqrt (by linarith)]
    ring
  have hu_sq : ∑ c : Fin d, (u c) ^ 2 = 1 := by
    have h1 := EuclideanSpace.norm_sq_eq u
    rw [hu, one_pow] at h1
    simpa [Real.norm_eq_abs, sq_abs] using h1.symm
  have hv_sq : ∑ c : Fin d, (v c) ^ 2 = 1 := by
    have h1 := EuclideanSpace.norm_sq_eq v
    rw [hv, one_pow] at h1
    simpa [Real.norm_eq_abs, sq_abs] using h1.symm
  have huv : ∑ c : Fin d, u c * v c = t := by
    dsimp only [t]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm]
  -- Define continuous linear maps T₁ and T₂
  let T₁ : (Fin (k * d) → ℝ) →L[ℝ] (Fin k → ℝ × ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun g a => (∑ c : Fin d, g (finProdFinEquiv (a, c)) * u c,
          ∑ c : Fin d, g (finProdFinEquiv (a, c)) * v c)
        map_add' := fun g₁ g₂ => by
          ext a <;> simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun r g => by
          ext a <;> simp [mul_assoc, Finset.mul_sum] }
  let T₂ : (Fin k → ℝ × ℝ) →L[ℝ] (Fin k → ℝ × ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun w a => ((w a).1, t * (w a).1 + s * (w a).2)
        map_add' := fun w₁ w₂ => by
          ext a
          · simp
          · simp; ring
        map_smul' := fun r w => by
          ext a
          · simp
          · simp; ring }
  -- Express P.map projPair as (Measure.pi ...).map T₁
  let g : Fin (k * d) → Ω → ℝ :=
    fun z ω => R (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2 ω
  have hg_meas : ∀ z, Measurable (g z) := hR.1
  have hg_indep : iIndepFun g P := hR.2.1
  have hg_law : ∀ z, P.map (g z) = stdGauss := hR.2.2
  have hpi : P.map (fun ω z => g z ω) = Measure.pi (fun _ : Fin (k * d) => stdGauss) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun z => (hg_meas z).aemeasurable)).mp hg_indep]
    congr 1
    funext z
    exact hg_law z
  have hcomp : (fun ω (a : Fin k) => (∑ c : Fin d, R a c ω * u c, ∑ c : Fin d, R a c ω * v c)) =
      T₁ ∘ (fun ω z => g z ω) := by
    funext ω a
    dsimp only [T₁, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp_apply, g]
    simp only [Equiv.symm_apply_apply]
  rw [hcomp, ← Measure.map_map T₁.continuous.measurable (measurable_pi_lambda _ hg_meas), hpi]
  change (Measure.pi (fun _ : Fin (k * d) => stdGauss)).map T₁ = (stdGaussK k).map T₂
  -- Now prove equality of the two mapped probability measures via charFunDual
  have : IsProbabilityMeasure ((Measure.pi (fun _ : Fin (k * d) => stdGauss)).map T₁) :=
    Measure.isProbabilityMeasure_map T₁.continuous.measurable.aemeasurable
  have : IsProbabilityMeasure ((stdGaussK k).map T₂) :=
    Measure.isProbabilityMeasure_map T₂.continuous.measurable.aemeasurable
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_map_clm, charFunDual_map_clm]
  rw [charFunDual_pi, stdGaussK, charFunDual_pi]
  -- Evaluate LHS product
  simp_rw [charFunDual_real_gaussianReal]
  -- Evaluate RHS product using charFunDual_prod
  have hRHS_term : ∀ a : Fin k,
      charFunDual stdGauss2 ((L.comp T₂).comp (ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ × ℝ) a)) =
      Complex.exp (-((((L (Pi.single a (1, 0)) + t * L (Pi.single a (0, 1)) : ℝ) : ℂ) ^ 2 +
        ((s * L (Pi.single a (0, 1)) : ℝ) : ℂ) ^ 2) / 2)) := by
    intro a
    rw [stdGauss2, charFunDual_prod, charFunDual_real_gaussianReal, charFunDual_real_gaussianReal,
      ← Complex.exp_add]
    congr 1
    have h1 : (((L.comp T₂).comp (ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ × ℝ) a)).comp
        (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1 =
        L (Pi.single a (1, 0)) + t * L (Pi.single a (0, 1)) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.single_apply]
      have hT : T₂ (Pi.single a ((1 : ℝ), (0 : ℝ))) =
          (Pi.single a ((1 : ℝ), (0 : ℝ)) : Fin k → ℝ × ℝ) +
            t • (Pi.single a ((0 : ℝ), (1 : ℝ)) : Fin k → ℝ × ℝ) := by
        ext b
        · by_cases hba : b = a <;> simp [T₂, hba]
        · by_cases hba : b = a <;> simp [T₂, hba]
      rw [hT, map_add, map_smul, smul_eq_mul]
    have h2 : (((L.comp T₂).comp (ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ × ℝ) a)).comp
        (ContinuousLinearMap.inr ℝ ℝ ℝ)) 1 =
        s * L (Pi.single a ((0 : ℝ), (1 : ℝ))) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.single_apply]
      have hT : T₂ (Pi.single a ((0 : ℝ), (1 : ℝ))) =
          s • (Pi.single a ((0 : ℝ), (1 : ℝ)) : Fin k → ℝ × ℝ) := by
        ext b
        · by_cases hba : b = a <;> simp [T₂, hba]
        · by_cases hba : b = a <;> simp [T₂, hba]
      rw [hT, map_smul, smul_eq_mul]
    rw [h1, h2]
    ring
  simp_rw [hRHS_term, ← Complex.exp_sum]
  congr 1
  -- Evaluate LHS exponent sum by reindexing via finProdFinEquiv
  have hLHS_term : ∀ (a : Fin k) (c : Fin d),
      ((L.comp T₁).comp (ContinuousLinearMap.single ℝ (fun _ : Fin (k * d) => ℝ)
        (finProdFinEquiv (a, c)))) 1 =
      u c * L (Pi.single a ((1 : ℝ), (0 : ℝ))) + v c * L (Pi.single a ((0 : ℝ), (1 : ℝ))) := by
    intro a c
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
    have hT : T₁ (Pi.single (finProdFinEquiv (a, c)) (1 : ℝ)) =
        u c • (Pi.single a ((1 : ℝ), (0 : ℝ)) : Fin k → ℝ × ℝ) +
          v c • (Pi.single a ((0 : ℝ), (1 : ℝ)) : Fin k → ℝ × ℝ) := by
      ext b
      · by_cases hba : b = a
        · subst hba
          simp only [T₁, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
            Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Prod.fst_add,
            Prod.smul_fst, mul_one, mul_zero, add_zero]
          rw [Finset.sum_eq_single c]
          · simp
          · intro c' _ hc'
            have hne : finProdFinEquiv (b, c') ≠ finProdFinEquiv (b, c) := by
              intro h; exact hc' (congrArg Prod.snd (finProdFinEquiv.injective h))
            simp [Pi.single_eq_of_ne hne]
          · intro hc; exact (hc (Finset.mem_univ c)).elim
        · simp only [T₁, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
            Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hba, smul_zero, add_zero]
          apply Finset.sum_eq_zero
          intro c' _
          have hne : finProdFinEquiv (b, c') ≠ finProdFinEquiv (a, c) := by
            intro h; exact hba (congrArg Prod.fst (finProdFinEquiv.injective h))
          simp [Pi.single_eq_of_ne hne]
      · by_cases hba : b = a
        · subst hba
          simp only [T₁, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
            Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Prod.snd_add,
            Prod.smul_snd, mul_one, mul_zero, zero_add]
          rw [Finset.sum_eq_single c]
          · simp
          · intro c' _ hc'
            have hne : finProdFinEquiv (b, c') ≠ finProdFinEquiv (b, c) := by
              intro h; exact hc' (congrArg Prod.snd (finProdFinEquiv.injective h))
            simp [Pi.single_eq_of_ne hne]
          · intro hc; exact (hc (Finset.mem_univ c)).elim
        · simp only [T₁, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
            Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hba, smul_zero, add_zero]
          apply Finset.sum_eq_zero
          intro c' _
          have hne : finProdFinEquiv (b, c') ≠ finProdFinEquiv (a, c) := by
            intro h; exact hba (congrArg Prod.fst (finProdFinEquiv.injective h))
          simp [Pi.single_eq_of_ne hne]
    rw [hT, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [hLHS_term a]
  set α := L (Pi.single a (1, 0))
  set β := L (Pi.single a (0, 1))
  have hsum_real : ∑ c : Fin d, (u c * α + v c * β) ^ 2 =
      (α + t * β) ^ 2 + (s * β) ^ 2 := by
    calc ∑ c : Fin d, (u c * α + v c * β) ^ 2
        = ∑ c : Fin d, ((u c) ^ 2 * α ^ 2 + 2 * (u c * v c) * (α * β) + (v c) ^ 2 * β ^ 2) :=
          Finset.sum_congr rfl fun c _ => by ring
      _ = (∑ c, (u c) ^ 2) * α ^ 2 + 2 * (∑ c, u c * v c) * (α * β) + (∑ c, (v c) ^ 2) * β ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = α ^ 2 + 2 * t * (α * β) + β ^ 2 := by rw [hu_sq, hv_sq, huv]; ring
      _ = (α + t * β) ^ 2 + (s * β) ^ 2 := by
          have : β ^ 2 = (t ^ 2 + s ^ 2) * β ^ 2 := by rw [hts, one_mul]
          linarith
  have hsum_c : (∑ c : Fin d, (((u c * α + v c * β : ℝ) : ℂ) ^ 2)) =
      (((α + t * β : ℝ) : ℂ) ^ 2 + ((s * β : ℝ) : ℂ) ^ 2) := by
    exact_mod_cast hsum_real
  simp_rw [Finset.sum_neg_distrib, ← Finset.sum_div, hsum_c]

/-! ### Section 2: Elementary 1D and 2D Gaussian integrals & Schwinger formula -/

private lemma inv_sqrt_eq_integral {a : ℝ} (ha : 0 < a) :
    (Real.sqrt a)⁻¹ = (Real.sqrt π)⁻¹ * ∫ u in Ioi (0 : ℝ), u ^ (-(1 / 2 : ℝ)) * rexp (-a * u) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := -(1 / 2 : ℝ)) (b := a)
    zero_lt_one (by norm_num) ha
  simp only [rpow_one, div_one] at h
  have hq : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hq, Real.Gamma_one_half_eq] at h
  have hpow : a ^ (-(1 / 2 : ℝ)) = (Real.sqrt a)⁻¹ := by
    rw [Real.rpow_neg ha.le, Real.sqrt_eq_rpow]
  rw [hpow, mul_one] at h
  rw [h, mul_comm (a.sqrt)⁻¹, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr Real.pi_pos),
    one_mul]

private lemma integrable_of_integral_ne_zero' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (h : ∫ x, f x ∂μ ≠ 0) : Integrable f μ :=
  by_contra fun hn => h (integral_undef hn)

private lemma integral_mul_exp_neg_mul_sq_all {b : ℝ} (_hb : 0 < b) :
    ∫ x : ℝ, x * rexp (-b * x ^ 2) = 0 := by
  have hneg := integral_neg_eq_self (fun x : ℝ => x * rexp (-b * x ^ 2)) volume
  have hodd : (fun x : ℝ => -x * rexp (-b * (-x) ^ 2)) = fun x => -(x * rexp (-b * x ^ 2)) := by
    ext x; ring_nf
  rw [hodd, integral_neg] at hneg
  linarith

private lemma integral_sq_mul_exp_neg_mul_sq_all {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * rexp (-b * x ^ 2) = (2 * b)⁻¹ * Real.sqrt (π / b) := by
  have h_Ioi : ∫ x in Ioi (0 : ℝ), x ^ 2 * rexp (-b * x ^ 2) =
      (4 * b)⁻¹ * Real.sqrt (π / b) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (2 : ℝ)) (b := b)
      (by norm_num) (by norm_num) hb
    have hcongr : (∫ x in Ioi (0 : ℝ), x ^ 2 * rexp (-b * x ^ 2)) =
        ∫ x in Ioi (0 : ℝ), x ^ (2 : ℝ) * rexp (-b * x ^ (2 : ℝ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp
    rw [hcongr, h]
    have hG : Real.Gamma (((2 : ℝ) + 1) / 2) = (1 / 2) * Real.sqrt π := by
      have : ((2 : ℝ) + 1) / 2 = (1 / 2 : ℝ) + 1 := by norm_num
      rw [this, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    rw [hG]
    have hbpow : b ^ (-((2 : ℝ) + 1) / 2) = b⁻¹ * (Real.sqrt b)⁻¹ := by
      have : -((2 : ℝ) + 1) / 2 = (-1 : ℝ) + -(1 / 2 : ℝ) := by norm_num
      rw [this, Real.rpow_add hb, Real.rpow_neg_one, Real.rpow_neg hb.le, Real.sqrt_eq_rpow]
    rw [hbpow, Real.sqrt_div Real.pi_pos.le]
    field_simp
    ring
  have h_int_Ioi : IntegrableOn (fun x : ℝ => x ^ 2 * rexp (-b * x ^ 2)) (Ioi 0) :=
    integrable_of_integral_ne_zero' (by rw [h_Ioi]; positivity)
  have h_Iic : ∫ x in Iic (0 : ℝ), x ^ 2 * rexp (-b * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ 2 * rexp (-b * x ^ 2) := by
    have := integral_comp_neg_Ioi (0 : ℝ) (fun x : ℝ => x ^ 2 * rexp (-b * x ^ 2))
    simpa using this.symm
  have h_int_Iic : IntegrableOn (fun x : ℝ => x ^ 2 * rexp (-b * x ^ 2)) (Iic 0) :=
    integrable_of_integral_ne_zero' (by rw [h_Iic, h_Ioi]; positivity)
  have h_tot : Integrable (fun x : ℝ => x ^ 2 * rexp (-b * x ^ 2)) volume := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact h_int_Iic.union h_int_Ioi
  rw [← integral_add_compl measurableSet_Ioi h_tot, Set.compl_Ioi, h_Iic, h_Ioi]
  ring

private lemma integrable_mul_exp_neg_mul_sq_real {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x * rexp (-b * x ^ 2)) volume := by
  have h := (integrable_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa)).re
  convert h using 1
  ext x
  have h1 : (-(b : ℂ) * (x : ℂ) ^ 2) = ↑(-b * x ^ 2) := by push_cast; ring
  change x * rexp (-b * x ^ 2) = ((x : ℂ) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)).re
  rw [h1, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]

private lemma quad_complete_square (u v t s x z : ℝ) (hts : t ^ 2 + s ^ 2 = 1)
    (hv : 0 < v) :
    let α := 1 + 2 * v * s ^ 2;
    let β := 2 * v * t * s / α;
    let D := (1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2;
    let lam := D / α;
    -(x ^ 2 / 2) + -(z ^ 2 / 2) + (-u * x ^ 2 - v * (t * x + s * z) ^ 2) =
      -(α / 2) * (z + β * x) ^ 2 + -(lam / 2) * x ^ 2 := by
  intro α β D lam
  have hα : 0 < α := by positivity
  have hα_ne : α ≠ 0 := hα.ne'
  dsimp only [β, lam, D, α]
  field_simp
  have h1 : t ^ 2 = 1 - s ^ 2 := by linarith
  ring_nf
  rw [h1]
  ring

private lemma D_pos {u v t s : ℝ} (hu : 0 < u) (hv : 0 < v) (hts : t ^ 2 + s ^ 2 = 1) :
    0 < (1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2 := by
  have : (1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2 =
      1 + 2 * u + 2 * v + 4 * u * v * s ^ 2 := by
    have ht2 : t ^ 2 = 1 - s ^ 2 := by linarith
    rw [ht2]; ring
  rw [this]
  positivity

private lemma gaussianPDFReal_std (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * rexp (-(x ^ 2 / 2)) := by
  simp [gaussianPDFReal, neg_div]

private lemma eval_I0 {u v t s : ℝ} (hu : 0 < u) (hv : 0 < v) (hts : t ^ 2 + s ^ 2 = 1) :
    ∫ p : ℝ × ℝ, rexp (-u * p.1 ^ 2 - v * (t * p.1 + s * p.2) ^ 2) ∂stdGauss2 =
      ((1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2) ^ (-(1 / 2 : ℝ)) := by
  set α := 1 + 2 * v * s ^ 2
  set β := 2 * v * t * s / α
  set D := (1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2
  set lam := D / α
  have hα : 0 < α := by positivity
  have hD : 0 < D := D_pos hu hv hts
  have hlam : 0 < lam := div_pos hD hα
  have h_int : Integrable (fun p : ℝ × ℝ => rexp (-u * p.1 ^ 2 - v * (t * p.1 + s * p.2) ^ 2))
      stdGauss2 := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg p.1, sq_nonneg (t * p.1 + s * p.2)])
  rw [stdGauss2, integral_prod _ h_int]
  simp_rw [stdGauss, integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero, smul_eq_mul,
    gaussianPDFReal_std]
  have hstep : ∀ x : ℝ,
      (Real.sqrt (2 * π))⁻¹ * rexp (-(x ^ 2 / 2)) *
        ∫ z : ℝ, (Real.sqrt (2 * π))⁻¹ * rexp (-(z ^ 2 / 2)) *
          rexp (-u * x ^ 2 - v * (t * x + s * z) ^ 2) =
      (2 * π)⁻¹ * Real.sqrt (2 * π / α) * rexp (-(lam / 2) * x ^ 2) := by
    intro x
    have hinner : (∫ z : ℝ, (Real.sqrt (2 * π))⁻¹ * rexp (-(z ^ 2 / 2)) *
          rexp (-u * x ^ 2 - v * (t * x + s * z) ^ 2)) =
        (Real.sqrt (2 * π))⁻¹ * rexp (x ^ 2 / 2) * rexp (-(lam / 2) * x ^ 2) *
          ∫ z : ℝ, rexp (-(α / 2) * (z + β * x) ^ 2) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      dsimp only
      have hq := quad_complete_square u v t s x z hts hv
      have hexp : rexp (-(z ^ 2 / 2)) * rexp (-u * x ^ 2 - v * (t * x + s * z) ^ 2) =
          rexp (x ^ 2 / 2) * rexp (-(lam / 2) * x ^ 2) * rexp (-(α / 2) * (z + β * x) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        linarith
      rw [mul_assoc, hexp]
      ring
    rw [hinner, integral_add_right_eq_self (fun z => rexp (-(α / 2) * z ^ 2)) (β * x),
      integral_gaussian (α / 2)]
    have hpi : (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹ = (2 * π)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    have hexp0 : rexp (-(x ^ 2 / 2)) * rexp (x ^ 2 / 2) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hdiv : π / (α / 2) = 2 * π / α := by ring
    rw [hdiv]
    calc (Real.sqrt (2 * π))⁻¹ * rexp (-(x ^ 2 / 2)) *
          ((Real.sqrt (2 * π))⁻¹ * rexp (x ^ 2 / 2) * rexp (-(lam / 2) * x ^ 2) *
            Real.sqrt (2 * π / α))
        = ((Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹) *
            (rexp (-(x ^ 2 / 2)) * rexp (x ^ 2 / 2)) *
            Real.sqrt (2 * π / α) * rexp (-(lam / 2) * x ^ 2) := by ring
      _ = (2 * π)⁻¹ * Real.sqrt (2 * π / α) * rexp (-(lam / 2) * x ^ 2) := by
          rw [hpi, hexp0, mul_one]
  simp_rw [hstep, integral_const_mul, integral_gaussian (lam / 2)]
  have hdiv2 : π / (lam / 2) = 2 * π / lam := by ring
  rw [hdiv2]
  have hsqrt_prod : Real.sqrt (2 * π / α) * Real.sqrt (2 * π / lam) =
      (2 * π) * (Real.sqrt D)⁻¹ := by
    rw [← Real.sqrt_mul (by positivity)]
    have hmul : (2 * π / α) * (2 * π / lam) = (2 * π) ^ 2 / D := by
      dsimp only [lam]
      field_simp
    rw [hmul, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity), div_eq_mul_inv]
  rw [mul_assoc, hsqrt_prod, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul,
    Real.rpow_neg hD.le, Real.sqrt_eq_rpow]

private lemma eval_I1 {u v t s : ℝ} (hu : 0 < u) (hv : 0 < v) (hts : t ^ 2 + s ^ 2 = 1) :
    ∫ p : ℝ × ℝ, p.1 * (t * p.1 + s * p.2) *
      rexp (-u * p.1 ^ 2 - v * (t * p.1 + s * p.2) ^ 2) ∂stdGauss2 =
      t * ((1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2) ^ (-(3 / 2 : ℝ)) := by
  set α := 1 + 2 * v * s ^ 2
  set β := 2 * v * t * s / α
  set D := (1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2
  set lam := D / α
  have hα : 0 < α := by positivity
  have hD : 0 < D := D_pos hu hv hts
  have hlam : 0 < lam := div_pos hD hα
  -- First prove joint integrability on stdGauss2 (dominated by (p.1^2 + (t*p.1+s*p.2)^2) * exp(-u*p.1^2 - v*(...)^2) ≤ C)
  have h_int : Integrable (fun p : ℝ × ℝ => p.1 * (t * p.1 + s * p.2) *
      rexp (-u * p.1 ^ 2 - v * (t * p.1 + s * p.2) ^ 2)) stdGauss2 := by
    -- Elementary bound: for a > 0, |x| * exp(-a x^2) ≤ ... even simpler: x^2 * exp(-a x^2) ≤ 1/a!
    have hbd : ∀ a x : ℝ, 0 < a → a * x ^ 2 * rexp (-a * x ^ 2) ≤ 1 := by
      intro a x ha
      have h1 : 1 + a * x ^ 2 ≤ rexp (a * x ^ 2) := by
        linarith [Real.add_one_le_exp (a * x ^ 2)]
      have h2 : a * x ^ 2 ≤ rexp (a * x ^ 2) := by linarith
      calc a * x ^ 2 * rexp (-a * x ^ 2)
          ≤ rexp (a * x ^ 2) * rexp (-a * x ^ 2) := by
            gcongr
        _ = 1 := by rw [← Real.exp_add]; convert Real.exp_zero; ring
    refine Integrable.of_bound (by fun_prop) ((2 * u)⁻¹ + (2 * v)⁻¹) (ae_of_all _ fun p => ?_)
    set y := t * p.1 + s * p.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    have hAM : |p.1 * y| ≤ p.1 ^ 2 / 2 + y ^ 2 / 2 := by
      rw [abs_mul]
      have := sq_nonneg (|p.1| - |y|)
      rw [sub_sq, sq_abs, sq_abs] at this
      linarith
    have h1 : p.1 ^ 2 / 2 * rexp (-u * p.1 ^ 2 - v * y ^ 2) ≤ (2 * u)⁻¹ := by
      have hexp : rexp (-u * p.1 ^ 2 - v * y ^ 2) ≤ rexp (-u * p.1 ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])
      have hmul : p.1 ^ 2 / 2 * rexp (-u * p.1 ^ 2 - v * y ^ 2) ≤
          p.1 ^ 2 / 2 * rexp (-u * p.1 ^ 2) := by
        gcongr
      have hle := hbd u p.1 hu
      have h2u : 0 < 2 * u := by positivity
      calc p.1 ^ 2 / 2 * rexp (-u * p.1 ^ 2 - v * y ^ 2)
          ≤ p.1 ^ 2 / 2 * rexp (-u * p.1 ^ 2) := hmul
        _ = (2 * u)⁻¹ * (u * p.1 ^ 2 * rexp (-u * p.1 ^ 2)) := by field_simp
        _ ≤ (2 * u)⁻¹ * 1 := by gcongr
        _ = (2 * u)⁻¹ := mul_one _
    have h2 : y ^ 2 / 2 * rexp (-u * p.1 ^ 2 - v * y ^ 2) ≤ (2 * v)⁻¹ := by
      have hexp : rexp (-u * p.1 ^ 2 - v * y ^ 2) ≤ rexp (-v * y ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p.1])
      have hmul : y ^ 2 / 2 * rexp (-u * p.1 ^ 2 - v * y ^ 2) ≤
          y ^ 2 / 2 * rexp (-v * y ^ 2) := by
        gcongr
      have hle := hbd v y hv
      calc y ^ 2 / 2 * rexp (-u * p.1 ^ 2 - v * y ^ 2)
          ≤ y ^ 2 / 2 * rexp (-v * y ^ 2) := hmul
        _ = (2 * v)⁻¹ * (v * y ^ 2 * rexp (-v * y ^ 2)) := by field_simp
        _ ≤ (2 * v)⁻¹ * 1 := by gcongr
        _ = (2 * v)⁻¹ := mul_one _
    calc |p.1 * y| * rexp (-u * p.1 ^ 2 - v * y ^ 2)
        ≤ (p.1 ^ 2 / 2 + y ^ 2 / 2) * rexp (-u * p.1 ^ 2 - v * y ^ 2) := by
          gcongr
      _ = p.1 ^ 2 / 2 * rexp (-u * p.1 ^ 2 - v * y ^ 2) +
            y ^ 2 / 2 * rexp (-u * p.1 ^ 2 - v * y ^ 2) := add_mul _ _ _
      _ ≤ (2 * u)⁻¹ + (2 * v)⁻¹ := add_le_add h1 h2
  rw [stdGauss2, integral_prod _ h_int]
  simp_rw [stdGauss, integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero, smul_eq_mul,
    gaussianPDFReal_std]
  have hts_lin : t - s * β = t / α := by
    dsimp only [β, α]
    have hα_ne : 1 + 2 * v * s ^ 2 ≠ 0 := hα.ne'
    field_simp
    ring
  have hstep : ∀ x : ℝ,
      (Real.sqrt (2 * π))⁻¹ * rexp (-(x ^ 2 / 2)) *
        ∫ z : ℝ, (Real.sqrt (2 * π))⁻¹ * rexp (-(z ^ 2 / 2)) *
          (x * (t * x + s * z) * rexp (-u * x ^ 2 - v * (t * x + s * z) ^ 2)) =
      (2 * π)⁻¹ * (t / α) * Real.sqrt (2 * π / α) * (x ^ 2 * rexp (-(lam / 2) * x ^ 2)) := by
    intro x
    have hinner : (∫ z : ℝ, (Real.sqrt (2 * π))⁻¹ * rexp (-(z ^ 2 / 2)) *
          (x * (t * x + s * z) * rexp (-u * x ^ 2 - v * (t * x + s * z) ^ 2))) =
        (Real.sqrt (2 * π))⁻¹ * rexp (x ^ 2 / 2) * rexp (-(lam / 2) * x ^ 2) *
          ∫ z : ℝ, ((t / α) * x ^ 2 + s * x * (z + β * x)) * rexp (-(α / 2) * (z + β * x) ^ 2) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      dsimp only
      have hq := quad_complete_square u v t s x z hts hv
      have hexp : rexp (-(z ^ 2 / 2)) * rexp (-u * x ^ 2 - v * (t * x + s * z) ^ 2) =
          rexp (x ^ 2 / 2) * rexp (-(lam / 2) * x ^ 2) * rexp (-(α / 2) * (z + β * x) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        linarith
      have hlin : x * (t * x + s * z) = (t / α) * x ^ 2 + s * x * (z + β * x) := by
        rw [← hts_lin]; ring
      calc (Real.sqrt (2 * π))⁻¹ * rexp (-(z ^ 2 / 2)) *
              (x * (t * x + s * z) * rexp (-u * x ^ 2 - v * (t * x + s * z) ^ 2))
          = (Real.sqrt (2 * π))⁻¹ * (x * (t * x + s * z)) *
              (rexp (-(z ^ 2 / 2)) * rexp (-u * x ^ 2 - v * (t * x + s * z) ^ 2)) := by ring
        _ = (Real.sqrt (2 * π))⁻¹ * ((t / α) * x ^ 2 + s * x * (z + β * x)) *
              (rexp (x ^ 2 / 2) * rexp (-(lam / 2) * x ^ 2) * rexp (-(α / 2) * (z + β * x) ^ 2)) := by
              rw [hlin, hexp]
        _ = _ := by ring
    rw [hinner]
    have hshift := integral_add_right_eq_self (μ := volume)
      (fun z : ℝ => ((t / α) * x ^ 2 + s * x * z) * rexp (-(α / 2) * z ^ 2)) (β * x)
    rw [hshift]
    have hsplit : (∫ z : ℝ, ((t / α) * x ^ 2 + s * x * z) * rexp (-(α / 2) * z ^ 2)) =
        (t / α) * x ^ 2 * Real.sqrt (2 * π / α) := by
      have h_eq : (fun z : ℝ => ((t / α) * x ^ 2 + s * x * z) * rexp (-(α / 2) * z ^ 2)) =
          (fun z => (t / α) * x ^ 2 * rexp (-(α / 2) * z ^ 2) +
            s * x * (z * rexp (-(α / 2) * z ^ 2))) := by
        ext z; ring
      rw [h_eq, integral_add ((integrable_exp_neg_mul_sq (by positivity)).const_mul _)
        ((integrable_mul_exp_neg_mul_sq_real (by positivity)).const_mul _)]
      rw [integral_const_mul, integral_const_mul, integral_gaussian (α / 2),
        integral_mul_exp_neg_mul_sq_all (by positivity), mul_zero, add_zero]
      have hdiv : π / (α / 2) = 2 * π / α := by ring
      rw [hdiv]
    rw [hsplit]
    have hpi : (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹ = (2 * π)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    have hexp0 : rexp (-(x ^ 2 / 2)) * rexp (x ^ 2 / 2) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc (Real.sqrt (2 * π))⁻¹ * rexp (-(x ^ 2 / 2)) *
          ((Real.sqrt (2 * π))⁻¹ * rexp (x ^ 2 / 2) * rexp (-(lam / 2) * x ^ 2) *
            ((t / α) * x ^ 2 * Real.sqrt (2 * π / α)))
        = ((Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹) *
            (rexp (-(x ^ 2 / 2)) * rexp (x ^ 2 / 2)) *
            (t / α) * Real.sqrt (2 * π / α) * (x ^ 2 * rexp (-(lam / 2) * x ^ 2)) := by ring
      _ = (2 * π)⁻¹ * (t / α) * Real.sqrt (2 * π / α) * (x ^ 2 * rexp (-(lam / 2) * x ^ 2)) := by
          rw [hpi, hexp0, mul_one]
  simp_rw [hstep, integral_const_mul, integral_sq_mul_exp_neg_mul_sq_all (b := lam / 2) (by positivity)]
  have hdiv2 : π / (lam / 2) = 2 * π / lam := by ring
  have h2lam : 2 * (lam / 2) = lam := by ring
  rw [hdiv2, h2lam]
  have hsqrt_prod : Real.sqrt (2 * π / α) * Real.sqrt (2 * π / lam) =
      (2 * π) * (Real.sqrt D)⁻¹ := by
    rw [← Real.sqrt_mul (by positivity)]
    have hmul : (2 * π / α) * (2 * π / lam) = (2 * π) ^ 2 / D := by
      dsimp only [lam]; field_simp
    rw [hmul, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity), div_eq_mul_inv]
  have hD_pow : D ^ (-(3 / 2 : ℝ)) = D⁻¹ * (Real.sqrt D)⁻¹ := by
    have : -(3 / 2 : ℝ) = (-1 : ℝ) + -(1 / 2 : ℝ) := by norm_num
    rw [this, Real.rpow_add hD, Real.rpow_neg_one, Real.rpow_neg hD.le, Real.sqrt_eq_rpow]
  have hαlam : α * lam = D := by dsimp only [lam]; field_simp
  rw [hD_pow]
  calc (2 * π)⁻¹ * (t / α) * Real.sqrt (2 * π / α) * (lam⁻¹ * Real.sqrt (2 * π / lam))
      = (2 * π)⁻¹ * (Real.sqrt (2 * π / α) * Real.sqrt (2 * π / lam)) * (t * (α * lam)⁻¹) := by
        rw [mul_inv]; ring
    _ = (2 * π)⁻¹ * ((2 * π) * (Real.sqrt D)⁻¹) * (t * D⁻¹) := by
        rw [hsqrt_prod, hαlam]
    _ = t * (D⁻¹ * (Real.sqrt D)⁻¹) := by
        have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
        field_simp

/-! ### Section 3: Evaluating the k-dimensional Gaussian expectation inside Fubini -/

private lemma eval_inner_k {k : ℕ} (hk : 1 ≤ k) {u v t s : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hts : t ^ 2 + s ^ 2 = 1) :
    ∫ w : Fin k → ℝ × ℝ,
      (∑ a : Fin k, (w a).1 * (t * (w a).1 + s * (w a).2)) *
      rexp (-u * (∑ b : Fin k, (w b).1 ^ 2) - v * (∑ b : Fin k, (t * (w b).1 + s * (w b).2) ^ 2))
      ∂(stdGaussK k) =
      (k : ℝ) * t * ((1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2) ^ (-((k : ℝ) / 2 + 1)) := by
  set D := (1 + 2 * u) * (1 + 2 * v) - 4 * u * v * t ^ 2
  have hD : 0 < D := D_pos hu hv hts
  have hfactor : ∀ (a : Fin k) (w : Fin k → ℝ × ℝ),
      (w a).1 * (t * (w a).1 + s * (w a).2) *
        rexp (-u * (∑ b : Fin k, (w b).1 ^ 2) - v * (∑ b : Fin k, (t * (w b).1 + s * (w b).2) ^ 2)) =
      ∏ b : Fin k,
        ((if b = a then (w b).1 * (t * (w b).1 + s * (w b).2) else 1) *
          rexp (-u * (w b).1 ^ 2 - v * (t * (w b).1 + s * (w b).2) ^ 2)) := by
    intro a w
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    have hprod_ite : (∏ b : Fin k, if b = a then (w b).1 * (t * (w b).1 + s * (w b).2) else 1) =
        (w a).1 * (t * (w a).1 + s * (w a).2) := by
      rw [Finset.prod_eq_single a]
      · simp
      · intro b _ hba; simp [hba]
      · intro h; exact (h (Finset.mem_univ a)).elim
    rw [hprod_ite]
    congr 2
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- Integrability of each summand (same bound as in eval_I1)
  have h_int_a : ∀ a : Fin k, Integrable (fun w : Fin k → ℝ × ℝ =>
      (w a).1 * (t * (w a).1 + s * (w a).2) *
        rexp (-u * (∑ b : Fin k, (w b).1 ^ 2) - v * (∑ b : Fin k, (t * (w b).1 + s * (w b).2) ^ 2)))
      (stdGaussK k) := by
    intro a
    refine Integrable.of_bound (by fun_prop) ((2 * u)⁻¹ + (2 * v)⁻¹) (ae_of_all _ fun w => ?_)
    have hexp_le : rexp (-u * (∑ b : Fin k, (w b).1 ^ 2) -
        v * (∑ b : Fin k, (t * (w b).1 + s * (w b).2) ^ 2)) ≤
        rexp (-u * (w a).1 ^ 2 - v * (t * (w a).1 + s * (w a).2) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have h1 : (w a).1 ^ 2 ≤ ∑ b : Fin k, (w b).1 ^ 2 :=
        Finset.single_le_sum (fun b _ => sq_nonneg (w b).1) (Finset.mem_univ a)
      have h2 : (t * (w a).1 + s * (w a).2) ^ 2 ≤ ∑ b : Fin k, (t * (w b).1 + s * (w b).2) ^ 2 :=
        Finset.single_le_sum (fun b _ => sq_nonneg (t * (w b).1 + s * (w b).2)) (Finset.mem_univ a)
      nlinarith
    set x := (w a).1
    set y := t * (w a).1 + s * (w a).2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    have hAM : |x * y| ≤ x ^ 2 / 2 + y ^ 2 / 2 := by
      rw [abs_mul]
      have := sq_nonneg (|x| - |y|)
      rw [sub_sq, sq_abs, sq_abs] at this
      linarith
    have hbd : ∀ r z : ℝ, 0 < r → r * z ^ 2 * rexp (-r * z ^ 2) ≤ 1 := by
      intro r z hr
      have h2 : r * z ^ 2 ≤ rexp (r * z ^ 2) := by linarith [Real.add_one_le_exp (r * z ^ 2)]
      calc r * z ^ 2 * rexp (-r * z ^ 2)
          ≤ rexp (r * z ^ 2) * rexp (-r * z ^ 2) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; convert Real.exp_zero; ring
    have h1 : x ^ 2 / 2 * rexp (-u * x ^ 2 - v * y ^ 2) ≤ (2 * u)⁻¹ := by
      have hexp : rexp (-u * x ^ 2 - v * y ^ 2) ≤ rexp (-u * x ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])
      calc x ^ 2 / 2 * rexp (-u * x ^ 2 - v * y ^ 2)
          ≤ x ^ 2 / 2 * rexp (-u * x ^ 2) := by gcongr
        _ = (2 * u)⁻¹ * (u * x ^ 2 * rexp (-u * x ^ 2)) := by field_simp
        _ ≤ (2 * u)⁻¹ * 1 := by gcongr; exact hbd u x hu
        _ = (2 * u)⁻¹ := mul_one _
    have h2 : y ^ 2 / 2 * rexp (-u * x ^ 2 - v * y ^ 2) ≤ (2 * v)⁻¹ := by
      have hexp : rexp (-u * x ^ 2 - v * y ^ 2) ≤ rexp (-v * y ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
      calc y ^ 2 / 2 * rexp (-u * x ^ 2 - v * y ^ 2)
          ≤ y ^ 2 / 2 * rexp (-v * y ^ 2) := by gcongr
        _ = (2 * v)⁻¹ * (v * y ^ 2 * rexp (-v * y ^ 2)) := by field_simp
        _ ≤ (2 * v)⁻¹ * 1 := by gcongr; exact hbd v y hv
        _ = (2 * v)⁻¹ := mul_one _
    calc |x * y| * rexp (-u * (∑ b, (w b).1 ^ 2) - v * (∑ b, (t * (w b).1 + s * (w b).2) ^ 2))
        ≤ |x * y| * rexp (-u * x ^ 2 - v * y ^ 2) := by gcongr
      _ ≤ (x ^ 2 / 2 + y ^ 2 / 2) * rexp (-u * x ^ 2 - v * y ^ 2) := by gcongr
      _ = x ^ 2 / 2 * rexp (-u * x ^ 2 - v * y ^ 2) + y ^ 2 / 2 * rexp (-u * x ^ 2 - v * y ^ 2) :=
          add_mul _ _ _
      _ ≤ (2 * u)⁻¹ + (2 * v)⁻¹ := add_le_add h1 h2
  have hsum_eq : (fun w : Fin k → ℝ × ℝ =>
      (∑ a : Fin k, (w a).1 * (t * (w a).1 + s * (w a).2)) *
        rexp (-u * (∑ b : Fin k, (w b).1 ^ 2) - v * (∑ b : Fin k, (t * (w b).1 + s * (w b).2) ^ 2))) =
      fun w => ∑ a : Fin k, (w a).1 * (t * (w a).1 + s * (w a).2) *
        rexp (-u * (∑ b : Fin k, (w b).1 ^ 2) - v * (∑ b : Fin k, (t * (w b).1 + s * (w b).2) ^ 2)) := by
    ext w; rw [Finset.sum_mul]
  rw [hsum_eq, integral_finsetSum _ (fun a _ => h_int_a a)]
  have hterm : ∀ a : Fin k,
      (∫ w : Fin k → ℝ × ℝ, (w a).1 * (t * (w a).1 + s * (w a).2) *
        rexp (-u * (∑ b : Fin k, (w b).1 ^ 2) - v * (∑ b : Fin k, (t * (w b).1 + s * (w b).2) ^ 2))
        ∂(stdGaussK k)) = t * D ^ (-((k : ℝ) / 2 + 1)) := by
    intro a
    simp_rw [hfactor a]
    rw [stdGaussK, integral_fintype_prod_eq_prod
      (f := fun b (p : ℝ × ℝ) => (if b = a then p.1 * (t * p.1 + s * p.2) else 1) *
        rexp (-u * p.1 ^ 2 - v * (t * p.1 + s * p.2) ^ 2))]
    have hprod_eval : (∏ b : Fin k, ∫ p : ℝ × ℝ,
        (if b = a then p.1 * (t * p.1 + s * p.2) else 1) *
          rexp (-u * p.1 ^ 2 - v * (t * p.1 + s * p.2) ^ 2) ∂stdGauss2) =
        (t * D ^ (-(3 / 2 : ℝ))) * (D ^ (-(1 / 2 : ℝ))) ^ (k - 1) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
      congr 1
      · simp only [ite_true]
        exact eval_I1 hu hv hts
      · calc ∏ b ∈ Finset.univ.erase a, ∫ p : ℝ × ℝ,
              (if b = a then p.1 * (t * p.1 + s * p.2) else 1) *
                rexp (-u * p.1 ^ 2 - v * (t * p.1 + s * p.2) ^ 2) ∂stdGauss2
            = ∏ b ∈ Finset.univ.erase a, D ^ (-(1 / 2 : ℝ)) := by
              refine Finset.prod_congr rfl fun b hb => ?_
              have hba : b ≠ a := (Finset.mem_erase.mp hb).1
              simp only [hba, ite_false, one_mul]
              exact eval_I0 hu hv hts
          _ = (D ^ (-(1 / 2 : ℝ))) ^ (k - 1) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ a),
                Finset.card_fin]
    rw [hprod_eval, mul_assoc]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, ← Real.rpow_add hD]
    congr 1
    rw [Nat.cast_sub hk, Nat.cast_one]
    ring
  simp_rw [hterm, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  ring

/-! ### Section 4: Almost-everywhere nonzero norms & Fubini swap -/

private lemma ae_pos_norms {k : ℕ} (hk : 1 ≤ k) {t s : ℝ} (hts : t ^ 2 + s ^ 2 = 1) :
    ∀ᵐ w ∂(stdGaussK k),
      0 < ∑ a : Fin k, (w a).1 ^ 2 ∧ 0 < ∑ a : Fin k, (t * (w a).1 + s * (w a).2) ^ 2 := by
  let a0 : Fin k := ⟨0, hk⟩
  have hmap : (stdGaussK k).map (fun w => w a0) = stdGauss2 := by
    simpa [stdGaussK] using (MeasureTheory.measurePreserving_eval (fun _ : Fin k => stdGauss2) a0).map_eq
  have h1 : stdGauss2 {p : ℝ × ℝ | p.1 = 0} = 0 := by
    have heq : {p : ℝ × ℝ | p.1 = 0} = ({(0 : ℝ)} : Set ℝ) ×ˢ Set.univ := by ext p; simp
    rw [heq, stdGauss2, Measure.prod_prod]
    have h0 : stdGauss {0} = 0 :=
      gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp)
    simp [h0]
  have h2 : stdGauss2 {p : ℝ × ℝ | t * p.1 + s * p.2 = 0} = 0 := by
    by_cases hs : s = 0
    · have ht : t ≠ 0 := by
        intro ht0; rw [ht0, hs] at hts; norm_num at hts
      have heq : {p : ℝ × ℝ | t * p.1 + s * p.2 = 0} = {p : ℝ × ℝ | p.1 = 0} := by
        ext p; simp [hs, ht]
      rw [heq]; exact h1
    · rw [stdGauss2, Measure.prod_apply (measurableSet_eq_fun (by fun_prop) measurable_const)]
      have hslice : ∀ x : ℝ, stdGauss {z : ℝ | t * x + s * z = 0} = 0 := by
        intro x
        have heq : {z : ℝ | t * x + s * z = 0} = {-(t * x / s)} := by
          ext z
          simp only [Set.mem_singleton_iff]
          show t * x + s * z = 0 ↔ z = -(t * x / s)
          constructor
          · intro h; field_simp; linarith
          · intro h; rw [h]; field_simp; ring
        rw [heq]
        exact gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp)
      have hpre_eq : ∀ x : ℝ, Prod.mk x ⁻¹' {p : ℝ × ℝ | t * p.1 + s * p.2 = 0} =
          {z : ℝ | t * x + s * z = 0} := fun _ => rfl
      simp_rw [hpre_eq, hslice, lintegral_zero]
  have hbad1 : stdGaussK k {w : Fin k → ℝ × ℝ | (w a0).1 = 0} = 0 := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 = 0} :=
      measurableSet_eq_fun measurable_fst measurable_const
    have hpre : {w : Fin k → ℝ × ℝ | (w a0).1 = 0} = (fun w => w a0) ⁻¹' {p : ℝ × ℝ | p.1 = 0} := rfl
    rw [hpre, ← Measure.map_apply (measurable_pi_apply a0) hmeas, hmap, h1]
  have hbad2 : stdGaussK k {w : Fin k → ℝ × ℝ | t * (w a0).1 + s * (w a0).2 = 0} = 0 := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | t * p.1 + s * p.2 = 0} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    have hpre : {w : Fin k → ℝ × ℝ | t * (w a0).1 + s * (w a0).2 = 0} =
        (fun w => w a0) ⁻¹' {p : ℝ × ℝ | t * p.1 + s * p.2 = 0} := rfl
    rw [hpre, ← Measure.map_apply (measurable_pi_apply a0) hmeas, hmap, h2]
  have hae1 : ∀ᵐ w ∂(stdGaussK k), (w a0).1 ≠ 0 := by
    rw [ae_iff]; simpa using hbad1
  have hae2 : ∀ᵐ w ∂(stdGaussK k), t * (w a0).1 + s * (w a0).2 ≠ 0 := by
    rw [ae_iff]; simpa using hbad2
  filter_upwards [hae1, hae2] with w hw1 hw2
  constructor
  · exact lt_of_lt_of_le (sq_pos_of_ne_zero hw1)
      (Finset.single_le_sum (fun b _ => sq_nonneg (w b).1) (Finset.mem_univ a0))
  · exact lt_of_lt_of_le (sq_pos_of_ne_zero hw2)
      (Finset.single_le_sum (fun b _ => sq_nonneg (t * (w b).1 + s * (w b).2)) (Finset.mem_univ a0))

/-! ### Section 5: Binomial series, Gamma-Pochhammer, and Beta integral -/

private lemma gamma_add_nat {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.Gamma (a + n) = (ascPochhammer ℝ n).eval a * Real.Gamma a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), ih,
      ascPochhammer_succ_eval]
    ring

private lemma ring_choose_eq_ascPochhammer (c : ℝ) (n : ℕ) :
    Ring.choose (c + n - 1) n = (n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c := by
  simp only [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_cast, Polynomial.ascPochhammer_smeval_eq_eval, smul_eq_mul]
  rw [show c + (n : ℝ) - 1 - (n : ℝ) + 1 = c by ring]

private lemma hasSum_one_div_one_sub_rpow {c x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => ((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c) * x ^ n)
      ((1 - x) ^ (-c)) := by
  have hps := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero c
  have hxball : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast (show ‖x‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  have hsum := hps.hasSum hxball
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hsum
  have hrhs : 1 / (1 - x) ^ c = (1 - x) ^ (-c) := by
    rw [one_div, Real.rpow_neg (by linarith)]
  rw [hrhs] at hsum
  exact hsum.congr_fun fun n => by rw [ring_choose_eq_ascPochhammer]

private lemma beta_integral_Ioo {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ∫ p in Ioo (0 : ℝ) 1, p ^ (u - 1) * (1 - p) ^ (v - 1) =
      Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  have hC := Complex.betaIntegral_eq_Gamma_mul_div (u : ℂ) (v : ℂ) (by simpa) (by simpa)
  rw [Complex.betaIntegral] at hC
  have hre : ((∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1)).re) =
      (Real.Gamma u * Real.Gamma v / Real.Gamma (u + v)) := by
    rw [hC]
    have h1 : (Complex.Gamma (u : ℂ) * Complex.Gamma (v : ℂ) / Complex.Gamma ((u : ℂ) + (v : ℂ))) =
        ((Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) : ℝ) : ℂ) := by
      push_cast
      rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_add, Complex.Gamma_ofReal]
    rw [h1, Complex.ofReal_re]
  rw [← hre, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hcongr : (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1)) =
      ∫ x in Ioo (0 : ℝ) 1, ((x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
    push_cast
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
    push_cast
    rfl
  rw [hcongr, integral_complex_ofReal, Complex.ofReal_re]

private lemma integrableOn_beta_Ioo {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun p : ℝ => p ^ (u - 1) * (1 - p) ^ (v - 1)) (Ioo 0 1) volume := by
  have hC := Complex.betaIntegral_convergent (u := (u : ℂ)) (v := (v : ℂ)) (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hC
  have hre := hC.re
  refine hre.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : 0 ≤ x := hx.1.le
  have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
  have h1 : (x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1) =
      ((x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
    push_cast; rfl
  change ((x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1)).re =
    x ^ (u - 1) * (1 - x) ^ (v - 1)
  rw [h1, Complex.ofReal_re]

/-! ### Section 6: Change of variables (0, ∞) ↔ (0, 1) and final hypergeometric evaluation -/

private noncomputable def phi (p : ℝ) : ℝ := p / (2 * (1 - p))

private lemma phi_image_Ioo : phi '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
  ext u
  simp only [Set.mem_image, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
    unfold phi
    have : 0 < 1 - p := by linarith
    positivity
  · intro hu
    refine ⟨2 * u / (1 + 2 * u), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · unfold phi
      have h1 : 1 - 2 * u / (1 + 2 * u) = 1 / (1 + 2 * u) := by
        field_simp; ring
      rw [h1]
      field_simp

private lemma phi_injOn : InjOn phi (Ioo (0 : ℝ) 1) := by
  intro p hp q hq h
  unfold phi at h
  have hp1 : 1 - p ≠ 0 := by linarith [hp.2]
  have hq1 : 1 - q ≠ 0 := by linarith [hq.2]
  field_simp at h
  linarith

private lemma phi_hasDerivWithinAt {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt phi (1 / (2 * (1 - p) ^ 2)) (Ioo 0 1) p := by
  have hp1 : 1 - p ≠ 0 := by linarith [hp.2]
  have h1 : HasDerivAt (fun x : ℝ => 2 * (1 - x)) (-2) p := by
    simpa using ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).const_mul 2
  have h2 := (hasDerivAt_id p).div h1 (by positivity : 2 * (1 - p) ≠ 0)
  refine h2.hasDerivWithinAt.congr_deriv ?_
  dsimp only [id]
  field_simp
  ring

private lemma change_var_integrand {k : ℕ} {t p q : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) (ht : t ^ 2 ≤ 1) :
    |1 / (2 * (1 - p) ^ 2)| * (|1 / (2 * (1 - q) ^ 2)| *
      ((phi p) ^ (-(1 / 2 : ℝ)) * (phi q) ^ (-(1 / 2 : ℝ)) *
        ((1 + 2 * phi p) * (1 + 2 * phi q) - 4 * phi p * phi q * t ^ 2) ^
          (-((k : ℝ) / 2 + 1)))) =
    (1 / 2 : ℝ) * (p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2) *
      (q ^ (-(1 / 2 : ℝ)) * (1 - q) ^ (((k : ℝ) - 1) / 2)) *
      (1 - p * q * t ^ 2) ^ (-((k : ℝ) / 2 + 1))) := by
  have hp0 : 0 < p := hp.1
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hq0 : 0 < q := hq.1
  have hq1 : 0 < 1 - q := by linarith [hq.2]
  have hpqt : 0 < 1 - p * q * t ^ 2 := by
    have h1 : p * q < 1 := by nlinarith [hp.2, hq.2]
    nlinarith [mul_nonneg hp0.le hq0.le]
  have h1p : 1 + 2 * phi p = (1 - p)⁻¹ := by unfold phi; field_simp; ring
  have h1q : 1 + 2 * phi q = (1 - q)⁻¹ := by unfold phi; field_simp; ring
  have hD : (1 + 2 * phi p) * (1 + 2 * phi q) - 4 * phi p * phi q * t ^ 2 =
      (1 - p)⁻¹ * (1 - q)⁻¹ * (1 - p * q * t ^ 2) := by
    rw [h1p, h1q]; unfold phi; field_simp; ring
  rw [hD, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hDrpow : ((1 - p)⁻¹ * (1 - q)⁻¹ * (1 - p * q * t ^ 2)) ^ (-((k : ℝ) / 2 + 1)) =
      (1 - p) ^ ((k : ℝ) / 2 + 1) * (1 - q) ^ ((k : ℝ) / 2 + 1) *
        (1 - p * q * t ^ 2) ^ (-((k : ℝ) / 2 + 1)) := by
    rw [Real.mul_rpow (by positivity) hpqt.le, Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow hp1.le, Real.inv_rpow hq1.le,
      ← Real.rpow_neg hp1.le, ← Real.rpow_neg hq1.le, neg_neg]
  rw [hDrpow]
  have hphi_rpow : ∀ r : ℝ, 0 < r → 0 < 1 - r →
      (1 / (2 * (1 - r) ^ 2)) * (phi r) ^ (-(1 / 2 : ℝ)) * (1 - r) ^ ((k : ℝ) / 2 + 1) =
        (Real.sqrt 2)⁻¹ * (r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (((k : ℝ) - 1) / 2)) := by
    intro r hr0 hr1
    have hdiv_rpow : (phi r) ^ (-(1 / 2 : ℝ)) =
        r ^ (-(1 / 2 : ℝ)) * ((2 : ℝ) ^ (1 / 2 : ℝ) * (1 - r) ^ (1 / 2 : ℝ)) := by
      unfold phi
      rw [Real.div_rpow hr0.le (by positivity), Real.mul_rpow zero_le_two hr1.le,
        div_eq_mul_inv, mul_inv, ← Real.rpow_neg zero_le_two, ← Real.rpow_neg hr1.le, neg_neg]
    rw [hdiv_rpow]
    have h2 : (2 : ℝ)⁻¹ * (2 : ℝ) ^ (1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
      rw [← Real.sqrt_eq_rpow]
      have hsq := Real.mul_self_sqrt zero_le_two
      field_simp
      linarith
    have hr_pow : ((1 - r) ^ 2)⁻¹ * (1 - r) ^ (1 / 2 : ℝ) * (1 - r) ^ ((k : ℝ) / 2 + 1) =
        (1 - r) ^ (((k : ℝ) - 1) / 2) := by
      have hsq : ((1 - r) ^ 2)⁻¹ = (1 - r) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hr1.le, Real.rpow_two]
      rw [hsq, ← Real.rpow_add hr1, ← Real.rpow_add hr1]
      congr 1; ring
    calc 1 / (2 * (1 - r) ^ 2) * (r ^ (-(1 / 2 : ℝ)) * ((2 : ℝ) ^ (1 / 2 : ℝ) * (1 - r) ^ (1 / 2 : ℝ))) *
            (1 - r) ^ ((k : ℝ) / 2 + 1)
        = ((2 : ℝ)⁻¹ * (2 : ℝ) ^ (1 / 2 : ℝ)) *
            (r ^ (-(1 / 2 : ℝ)) * (((1 - r) ^ 2)⁻¹ * (1 - r) ^ (1 / 2 : ℝ) * (1 - r) ^ ((k : ℝ) / 2 + 1))) := by
          rw [one_div, mul_inv]; ring
      _ = (Real.sqrt 2)⁻¹ * (r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (((k : ℝ) - 1) / 2)) := by
          rw [h2, hr_pow]
  have hsq2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt zero_le_two, one_div]
  calc 1 / (2 * (1 - p) ^ 2) * (1 / (2 * (1 - q) ^ 2) *
          ((phi p) ^ (-(1 / 2 : ℝ)) * (phi q) ^ (-(1 / 2 : ℝ)) *
            ((1 - p) ^ ((k : ℝ) / 2 + 1) * (1 - q) ^ ((k : ℝ) / 2 + 1) *
              (1 - p * q * t ^ 2) ^ (-((k : ℝ) / 2 + 1)))))
      = (1 / (2 * (1 - p) ^ 2) * (phi p) ^ (-(1 / 2 : ℝ)) * (1 - p) ^ ((k : ℝ) / 2 + 1)) *
          (1 / (2 * (1 - q) ^ 2) * (phi q) ^ (-(1 / 2 : ℝ)) * (1 - q) ^ ((k : ℝ) / 2 + 1)) *
          (1 - p * q * t ^ 2) ^ (-((k : ℝ) / 2 + 1)) := by ring
    _ = ((Real.sqrt 2)⁻¹ * (p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2))) *
          ((Real.sqrt 2)⁻¹ * (q ^ (-(1 / 2 : ℝ)) * (1 - q) ^ (((k : ℝ) - 1) / 2))) *
          (1 - p * q * t ^ 2) ^ (-((k : ℝ) / 2 + 1)) := by
        rw [hphi_rpow p hp0 hp1, hphi_rpow q hq0 hq1]
    _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) *
          (p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2) *
            (q ^ (-(1 / 2 : ℝ)) * (1 - q) ^ (((k : ℝ) - 1) / 2)) *
            (1 - p * q * t ^ 2) ^ (-((k : ℝ) / 2 + 1))) := by ring
    _ = _ := by rw [hsq2]

private lemma ascPochhammer_eval_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    positivity

private lemma main_model_eq {k : ℕ} (hk : 1 ≤ k) {t s : ℝ} (hts : t ^ 2 + s ^ 2 = 1) :
    (∫ w : Fin k → ℝ × ℝ,
      inner ℝ (unitVec (WithLp.toLp 2 (fun a : Fin k => (w a).1)))
        (unitVec (WithLp.toLp 2 (fun a : Fin k => t * (w a).1 + s * (w a).2)))
      ∂(stdGaussK k)) = F k t := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  let ν1 : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν : Measure (ℝ × ℝ) := ν1.prod ν1
  have hpos_ν : ∀ᵐ uv : ℝ × ℝ ∂ν, 0 < uv.1 ∧ 0 < uv.2 := by
    have hm : MeasurableSet {uv : ℝ × ℝ | 0 < uv.1 ∧ 0 < uv.2} := by
      have heq : {uv : ℝ × ℝ | 0 < uv.1 ∧ 0 < uv.2} = Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
        ext uv; simp
      rw [heq]
      exact measurableSet_Ioi.prod measurableSet_Ioi
    dsimp only [ν]
    rw [Measure.ae_prod_iff_ae_ae hm]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact ⟨hu, hv⟩
  let A : (Fin k → ℝ × ℝ) → ℝ := fun w => ∑ a : Fin k, (w a).1 ^ 2
  let B : (Fin k → ℝ × ℝ) → ℝ := fun w => ∑ a : Fin k, (t * (w a).1 + s * (w a).2) ^ 2
  let C : (Fin k → ℝ × ℝ) → ℝ := fun w => ∑ a : Fin k, (w a).1 * (t * (w a).1 + s * (w a).2)
  let Φ : (Fin k → ℝ × ℝ) → ℝ × ℝ → ℝ := fun w uv =>
    uv.1 ^ (-(1 / 2 : ℝ)) * uv.2 ^ (-(1 / 2 : ℝ)) * C w * rexp (-uv.1 * A w - uv.2 * B w)
  have hAe : ∀ᵐ w ∂(stdGaussK k), 0 < A w ∧ 0 < B w := ae_pos_norms hk hts
  -- Step A: express integrand a.e. as (1/π) * ∫ uv, Φ w uv ∂ν
  have hpointwise : ∀ w, 0 < A w → 0 < B w →
      inner ℝ (unitVec (WithLp.toLp 2 (fun a : Fin k => (w a).1)))
        (unitVec (WithLp.toLp 2 (fun a : Fin k => t * (w a).1 + s * (w a).2))) =
      π⁻¹ * ∫ uv : ℝ × ℝ, Φ w uv ∂ν := by
    intro w hAw hBw
    set x : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun a : Fin k => (w a).1)
    set y : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun a : Fin k => t * (w a).1 + s * (w a).2)
    have hx_norm : ‖x‖ = Real.sqrt (A w) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [x, Real.norm_eq_abs, sq_abs]
    have hy_norm : ‖y‖ = Real.sqrt (B w) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [y, Real.norm_eq_abs, sq_abs]
    have hxy : inner ℝ x y = C w := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [x, y, C, dotProduct, mul_comm]
    have hunit : inner ℝ (unitVec x) (unitVec y) =
        C w * (Real.sqrt (A w))⁻¹ * (Real.sqrt (B w))⁻¹ := by
      unfold unitVec
      rw [real_inner_smul_left, real_inner_smul_right, hx_norm, hy_norm, hxy]
      ring
    rw [hunit, inv_sqrt_eq_integral hAw, inv_sqrt_eq_integral hBw]
    have hprod_int : (∫ u in Ioi (0 : ℝ), u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u)) *
        (∫ v in Ioi (0 : ℝ), v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v)) =
        ∫ uv : ℝ × ℝ, (uv.1 ^ (-(1 / 2 : ℝ)) * rexp (-A w * uv.1)) *
          (uv.2 ^ (-(1 / 2 : ℝ)) * rexp (-B w * uv.2)) ∂ν :=
      (integral_prod_mul (μ := ν1) (ν := ν1)
        (fun u => u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u))
        (fun v => v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v))).symm
    have hpi : (Real.sqrt π)⁻¹ * (Real.sqrt π)⁻¹ = π⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt Real.pi_pos.le]
    calc C w * ((Real.sqrt π)⁻¹ * ∫ u in Ioi (0 : ℝ), u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u)) *
          ((Real.sqrt π)⁻¹ * ∫ v in Ioi (0 : ℝ), v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v))
        = ((Real.sqrt π)⁻¹ * (Real.sqrt π)⁻¹) * (C w *
            ((∫ u in Ioi (0 : ℝ), u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u)) *
             (∫ v in Ioi (0 : ℝ), v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v)))) := by ring
      _ = π⁻¹ * ∫ uv : ℝ × ℝ, C w * ((uv.1 ^ (-(1 / 2 : ℝ)) * rexp (-A w * uv.1)) *
            (uv.2 ^ (-(1 / 2 : ℝ)) * rexp (-B w * uv.2))) ∂ν := by
          rw [hpi, hprod_int, ← integral_const_mul]
      _ = π⁻¹ * ∫ uv : ℝ × ℝ, Φ w uv ∂ν := by
          congr 1
          refine integral_congr_ae (ae_of_all _ fun uv => ?_)
          dsimp only [Φ]
          have hexp : rexp (-uv.1 * A w - uv.2 * B w) = rexp (-A w * uv.1) * rexp (-B w * uv.2) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hexp]; ring
  -- Step B: joint integrability of Φ on (stdGaussK k).prod ν
  have hΦ_meas : AEStronglyMeasurable (Function.uncurry Φ) ((stdGaussK k).prod ν) := by
    have h : Measurable (Function.uncurry Φ) := by
      dsimp only [Function.uncurry, Φ, A, B, C]
      fun_prop
    exact h.aestronglyMeasurable
  have hΦ_int : Integrable (Function.uncurry Φ) ((stdGaussK k).prod ν) := by
    rw [integrable_prod_iff hΦ_meas]
    have hnorm_eval : ∀ w, 0 < A w → 0 < B w →
        Integrable (Φ w) ν ∧ ∫ uv, ‖Φ w uv‖ ∂ν ≤ π := by
      intro w hAw hBw
      have hfu : Integrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u)) ν1 := by
        refine integrable_of_integral_ne_zero' ?_
        have := inv_sqrt_eq_integral hAw
        intro hz; rw [hz, mul_zero] at this
        exact (inv_pos.mpr (Real.sqrt_pos.mpr hAw)).ne' this
      have hfv : Integrable (fun v : ℝ => v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v)) ν1 := by
        refine integrable_of_integral_ne_zero' ?_
        have := inv_sqrt_eq_integral hBw
        intro hz; rw [hz, mul_zero] at this
        exact (inv_pos.mpr (Real.sqrt_pos.mpr hBw)).ne' this
      have hmul := (hfu.mul_prod hfv).const_mul (C w)
      have hΦ_eq : Φ w = fun uv : ℝ × ℝ =>
          C w * ((uv.1 ^ (-(1 / 2 : ℝ)) * rexp (-A w * uv.1)) *
            (uv.2 ^ (-(1 / 2 : ℝ)) * rexp (-B w * uv.2))) := by
        ext uv; dsimp only [Φ]
        have hexp : rexp (-uv.1 * A w - uv.2 * B w) = rexp (-A w * uv.1) * rexp (-B w * uv.2) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hexp]; ring
      refine ⟨hΦ_eq ▸ hmul, ?_⟩
      have hnorm_ae : ∀ᵐ uv ∂ν, ‖Φ w uv‖ =
          |C w| * ((uv.1 ^ (-(1 / 2 : ℝ)) * rexp (-A w * uv.1)) *
            (uv.2 ^ (-(1 / 2 : ℝ)) * rexp (-B w * uv.2))) := by
        filter_upwards [hpos_ν] with uv ⟨hu, hv⟩
        rw [hΦ_eq, Real.norm_eq_abs, abs_mul]
        congr 1
        exact abs_of_nonneg (by positivity)
      rw [integral_congr_ae hnorm_ae, integral_const_mul]
      dsimp only [ν]
      rw [integral_prod_mul (μ := ν1) (ν := ν1)
        (fun u => u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u))
        (fun v => v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v))]
      have hiu : (∫ u, u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u) ∂ν1) =
          Real.sqrt π * (Real.sqrt (A w))⁻¹ := by
        have := inv_sqrt_eq_integral hAw
        have hpi_ne : (Real.sqrt π)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.mpr Real.pi_pos)
        calc ∫ u, u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u) ∂ν1
            = Real.sqrt π * ((Real.sqrt π)⁻¹ * ∫ u in Ioi (0 : ℝ), u ^ (-(1 / 2 : ℝ)) * rexp (-A w * u)) := by
              rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr Real.pi_pos), one_mul]
          _ = Real.sqrt π * (Real.sqrt (A w))⁻¹ := by rw [← this]
      have hiv : (∫ v, v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v) ∂ν1) =
          Real.sqrt π * (Real.sqrt (B w))⁻¹ := by
        have := inv_sqrt_eq_integral hBw
        calc ∫ v, v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v) ∂ν1
            = Real.sqrt π * ((Real.sqrt π)⁻¹ * ∫ v in Ioi (0 : ℝ), v ^ (-(1 / 2 : ℝ)) * rexp (-B w * v)) := by
              rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr Real.pi_pos), one_mul]
          _ = Real.sqrt π * (Real.sqrt (B w))⁻¹ := by rw [← this]
      rw [hiu, hiv]
      have hCS : |C w| ≤ Real.sqrt (A w) * Real.sqrt (B w) := by
        set x : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun a : Fin k => (w a).1)
        set y : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun a : Fin k => t * (w a).1 + s * (w a).2)
        have hx : ‖x‖ = Real.sqrt (A w) := by
          rw [EuclideanSpace.norm_eq]; congr 1
          exact Finset.sum_congr rfl fun a _ => by simp [x, Real.norm_eq_abs, sq_abs]
        have hy : ‖y‖ = Real.sqrt (B w) := by
          rw [EuclideanSpace.norm_eq]; congr 1
          exact Finset.sum_congr rfl fun a _ => by simp [y, Real.norm_eq_abs, sq_abs]
        have hxy : inner ℝ x y = C w := by
          rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [x, y, C, dotProduct, mul_comm]
        simpa [hx, hy, hxy] using abs_real_inner_le_norm x y
      calc |C w| * (Real.sqrt π * (Real.sqrt (A w))⁻¹ * (Real.sqrt π * (Real.sqrt (B w))⁻¹))
          = (Real.sqrt π * Real.sqrt π) * (|C w| * ((Real.sqrt (A w))⁻¹ * (Real.sqrt (B w))⁻¹)) := by ring
        _ = π * (|C w| * (Real.sqrt (A w) * Real.sqrt (B w))⁻¹) := by
            rw [Real.mul_self_sqrt Real.pi_pos.le, mul_inv]
        _ ≤ π * ((Real.sqrt (A w) * Real.sqrt (B w)) * (Real.sqrt (A w) * Real.sqrt (B w))⁻¹) := by
            gcongr
        _ = π := by
            rw [mul_inv_cancel₀ (mul_pos (Real.sqrt_pos.mpr hAw) (Real.sqrt_pos.mpr hBw)).ne', mul_one]
    refine ⟨?_, ?_⟩
    · filter_upwards [hAe] with w ⟨hAw, hBw⟩
      exact (hnorm_eval w hAw hBw).1
    · refine Integrable.of_bound ?_ π ?_
      · exact hΦ_meas.norm.integral_prod_right'
      · filter_upwards [hAe] with w ⟨hAw, hBw⟩
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact (hnorm_eval w hAw hBw).2
  -- Step C: apply Fubini and evaluate inner k-dim Gaussian integral
  have hLHS_fubini :
      (∫ w : Fin k → ℝ × ℝ,
        inner ℝ (unitVec (WithLp.toLp 2 (fun a : Fin k => (w a).1)))
          (unitVec (WithLp.toLp 2 (fun a : Fin k => t * (w a).1 + s * (w a).2)))
        ∂(stdGaussK k)) =
      π⁻¹ * ((k : ℝ) * t) * ∫ uv : ℝ × ℝ,
        uv.1 ^ (-(1 / 2 : ℝ)) * uv.2 ^ (-(1 / 2 : ℝ)) *
        ((1 + 2 * uv.1) * (1 + 2 * uv.2) - 4 * uv.1 * uv.2 * t ^ 2) ^ (-((k : ℝ) / 2 + 1)) ∂ν := by
    have hae_eq : ∀ᵐ w ∂(stdGaussK k),
        inner ℝ (unitVec (WithLp.toLp 2 (fun a : Fin k => (w a).1)))
          (unitVec (WithLp.toLp 2 (fun a : Fin k => t * (w a).1 + s * (w a).2))) =
        π⁻¹ * ∫ uv : ℝ × ℝ, Φ w uv ∂ν := by
      filter_upwards [hAe] with w ⟨hAw, hBw⟩ using hpointwise w hAw hBw
    rw [integral_congr_ae hae_eq, integral_const_mul, integral_integral_swap hΦ_int]
    have hinner_ae : ∀ᵐ uv ∂ν, (∫ w, Φ w uv ∂(stdGaussK k)) =
        ((k : ℝ) * t) * (uv.1 ^ (-(1 / 2 : ℝ)) * uv.2 ^ (-(1 / 2 : ℝ)) *
          ((1 + 2 * uv.1) * (1 + 2 * uv.2) - 4 * uv.1 * uv.2 * t ^ 2) ^ (-((k : ℝ) / 2 + 1))) := by
      filter_upwards [hpos_ν] with uv ⟨hu, hv⟩
      have hpull : (fun w => Φ w uv) = fun w =>
          (uv.1 ^ (-(1 / 2 : ℝ)) * uv.2 ^ (-(1 / 2 : ℝ))) *
            (C w * rexp (-uv.1 * A w - uv.2 * B w)) := by
        ext w; dsimp only [Φ]; ring
      rw [hpull, integral_const_mul, eval_inner_k hk hu hv hts]
      ring
    rw [integral_congr_ae hinner_ae, integral_const_mul]
    ring
  rw [hLHS_fubini]
  -- Handle t = 0 immediately!
  by_cases ht0 : t = 0
  · subst ht0
    simp [F]
  -- Now t ≠ 0: deduce integrability of the (u, v) integrand directly from hΦ_int!
  let g_uv : ℝ × ℝ → ℝ := fun uv =>
    uv.1 ^ (-(1 / 2 : ℝ)) * uv.2 ^ (-(1 / 2 : ℝ)) *
      ((1 + 2 * uv.1) * (1 + 2 * uv.2) - 4 * uv.1 * uv.2 * t ^ 2) ^ (-((k : ℝ) / 2 + 1))
  have hg_uv_int : Integrable g_uv ν := by
    have h1 : Integrable (fun uv => ∫ w, Φ w uv ∂(stdGaussK k)) ν := hΦ_int.integral_prod_right
    have h2 : ∀ᵐ uv ∂ν, ((k : ℝ) * t)⁻¹ * (∫ w, Φ w uv ∂(stdGaussK k)) = g_uv uv := by
      filter_upwards [hpos_ν] with uv ⟨hu, hv⟩
      have hpull : (fun w => Φ w uv) = fun w =>
          (uv.1 ^ (-(1 / 2 : ℝ)) * uv.2 ^ (-(1 / 2 : ℝ))) *
            (C w * rexp (-uv.1 * A w - uv.2 * B w)) := by
        ext w; dsimp only [Φ]; ring
      rw [hpull, integral_const_mul, eval_inner_k hk hu hv hts]
      have hkt : (k : ℝ) * t ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ht0
      dsimp only [g_uv]
      field_simp
    exact (h1.const_mul ((k : ℝ) * t)⁻¹).congr h2
  -- Step D: Change of variables (u, v) = (phi p, phi q) on Ioo 0 1, iterated in 1D
  let μ01 : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let c : ℝ := (k : ℝ) / 2 + 1
  have hc_pos : 0 < c := by positivity
  let G : ℝ → ℝ → ℝ := fun p q =>
    p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2) *
      (q ^ (-(1 / 2 : ℝ)) * (1 - q) ^ (((k : ℝ) - 1) / 2)) *
      (1 - p * q * t ^ 2) ^ (-c)
  have hinner_eq : ∀ p ∈ Ioo (0 : ℝ) 1,
      |1 / (2 * (1 - p) ^ 2)| • (∫ v in phi '' Ioo (0 : ℝ) 1, g_uv (phi p, v)) =
      (1 / 2 : ℝ) * ∫ q in Ioo (0 : ℝ) 1, G p q := by
    intro p hp
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun q hq => phi_hasDerivWithinAt hq) phi_injOn]
    simp_rw [smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun q hq => ?_
    exact change_var_integrand hp hq ht2
  have hcov_iter : (∫ uv : ℝ × ℝ, g_uv uv ∂ν) =
      (1 / 2 : ℝ) * ∫ p in Ioo (0 : ℝ) 1, (∫ q in Ioo (0 : ℝ) 1, G p q) := by
    rw [integral_prod _ hg_uv_int]
    change (∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), g_uv (u, v)) = _
    rw [← phi_image_Ioo]
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun p hp => phi_hasDerivWithinAt hp) phi_injOn]
    rw [setIntegral_congr_fun measurableSet_Ioo hinner_eq, integral_const_mul]
  have houter_int : IntegrableOn (fun p : ℝ => ∫ q in Ioo (0 : ℝ) 1, G p q) (Ioo 0 1) volume := by
    have h1 : IntegrableOn (fun u : ℝ => ∫ v in Ioi (0 : ℝ), g_uv (u, v)) (Ioi 0) volume :=
      hg_uv_int.integral_prod_left
    rw [← phi_image_Ioo, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      (fun p hp => phi_hasDerivWithinAt hp) phi_injOn] at h1
    have h2 : IntegrableOn (fun p : ℝ => (1 / 2 : ℝ) * ∫ q in Ioo (0 : ℝ) 1, G p q)
        (Ioo 0 1) volume :=
      h1.congr_fun hinner_eq measurableSet_Ioo
    have h3 := h2.const_mul (2 : ℝ)
    exact h3.congr (ae_of_all _ fun p => by ring)
  -- Helper: integral_tsum for nonnegative terms summing to an integrable function on μ01
  have h_nonneg_tsum_int : ∀ (F : ℕ → ℝ → ℝ) (S : ℝ → ℝ),
      (∀ n, Measurable (F n)) →
      (∀ n, ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ F n x) →
      (∀ x ∈ Ioo (0 : ℝ) 1, HasSum (fun n => F n x) (S x)) →
      IntegrableOn S (Ioo 0 1) volume →
      (∫ x in Ioo (0 : ℝ) 1, S x) = ∑' n, ∫ x in Ioo (0 : ℝ) 1, F n x := by
    intro F S hFm hFnn hFsum hSint
    have hS_ae : ∀ᵐ x ∂μ01, S x = ∑' n, F n x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hFsum x hx).tsum_eq.symm
    have hS_nn : ∀ᵐ x ∂μ01, 0 ≤ S x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hFsum x hx).nonneg (fun n => hFnn n x hx)
    have hlt : (∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ01) ≠ ⊤ := by
      have h1 : (∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ01) = ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ01 :=
        (lintegral_tsum fun n => (hFm n).enorm.aemeasurable).symm
      rw [h1]
      have h2 : ∀ᵐ x ∂μ01, (∑' n, ‖F n x‖ₑ) = ‖S x‖ₑ := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        have hF_enorm : ∀ n, ‖F n x‖ₑ = ENNReal.ofReal (F n x) := fun n => by
          rw [Real.enorm_eq_ofReal (hFnn n x hx)]
        have hS_enorm : ‖S x‖ₑ = ENNReal.ofReal (S x) :=
          Real.enorm_eq_ofReal ((hFsum x hx).nonneg (fun n => hFnn n x hx))
        simp_rw [hF_enorm, hS_enorm]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hFnn n x hx) (hFsum x hx).summable,
          (hFsum x hx).tsum_eq]
      rw [lintegral_congr_ae h2]
      exact hSint.2.ne
    change (∫ x, S x ∂μ01) = ∑' n, ∫ x, F n x ∂μ01
    rw [integral_congr_ae hS_ae, integral_tsum (fun n => (hFm n).aestronglyMeasurable) hlt]
  -- Step E1: Expand inner q-integral for each p ∈ Ioo 0 1
  let Bval : ℕ → ℝ := fun n =>
    Real.Gamma ((n : ℝ) + 1 / 2) * Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma (c + n)
  have hbeta_eval : ∀ n : ℕ,
      (∫ r in Ioo (0 : ℝ) 1, r ^ ((n : ℝ) - 1 / 2) * (1 - r) ^ (((k : ℝ) - 1) / 2)) = Bval n := by
    intro n
    have h := beta_integral_Ioo (u := (n : ℝ) + 1 / 2) (v := ((k : ℝ) + 1) / 2)
      (by positivity) (by positivity)
    have h1 : (n : ℝ) + 1 / 2 - 1 = (n : ℝ) - 1 / 2 := by ring
    have h2 : ((k : ℝ) + 1) / 2 - 1 = ((k : ℝ) - 1) / 2 := by ring
    have h3 : (n : ℝ) + 1 / 2 + ((k : ℝ) + 1) / 2 = c + n := by dsimp only [c]; ring
    rw [h1, h2, h3] at h
    exact h
  have hq_expand : ∀ p ∈ Ioo (0 : ℝ) 1,
      HasSum (fun n : ℕ =>
        ((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c * (t ^ 2) ^ n * Bval n) *
          (p ^ ((n : ℝ) - 1 / 2) * (1 - p) ^ (((k : ℝ) - 1) / 2)))
        (∫ q in Ioo (0 : ℝ) 1, G p q) := by
    intro p hp
    have hp0 : 0 < p := hp.1
    have hp1 : 0 < 1 - p := by linarith [hp.2]
    -- Show G p is integrable on Ioo 0 1 (bounded by constant * q^(-1/2) * (1-q)^((k-1)/2))
    have hGp_int : IntegrableOn (G p) (Ioo 0 1) volume := by
      have hbeta := integrableOn_beta_Ioo (u := (1 / 2 : ℝ)) (v := ((k : ℝ) + 1) / 2)
        (by positivity) (by positivity)
      have hdom := hbeta.const_mul
        (p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2) * (1 - p) ^ (-c))
      refine hdom.mono' (by dsimp only [G]; fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
      have hq0 : 0 < q := hq.1
      have hq1 : 0 < 1 - q := by linarith [hq.2]
      have hpqt_ge : 1 - p ≤ 1 - p * q * t ^ 2 := by
        have : p * q * t ^ 2 ≤ p := by
          have hqt : q * t ^ 2 ≤ 1 := by nlinarith [hq.2, sq_nonneg t]
          nlinarith
        linarith
      have hpow_le : (1 - p * q * t ^ 2) ^ (-c) ≤ (1 - p) ^ (-c) := by
        rw [Real.rpow_neg (by linarith), Real.rpow_neg hp1.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hp1 c)
          (Real.rpow_le_rpow hp1.le hpqt_ge hc_pos.le)
      have hpqt_pos : 0 < 1 - p * q * t ^ 2 := by linarith
      dsimp only [G]
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
      have h2 : ((k : ℝ) + 1) / 2 - 1 = ((k : ℝ) - 1) / 2 := by ring
      rw [h1, h2]
      have hrhs : p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2) * (1 - p) ^ (-c) *
          (q ^ (-(1 / 2 : ℝ)) * (1 - q) ^ (((k : ℝ) - 1) / 2)) =
          p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2) *
            (q ^ (-(1 / 2 : ℝ)) * (1 - q) ^ (((k : ℝ) - 1) / 2)) * (1 - p) ^ (-c) := by ring
      rw [hrhs]
      gcongr
    let Fq : ℕ → ℝ → ℝ := fun n q =>
      ((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c * (t ^ 2) ^ n) *
        (p ^ ((n : ℝ) - 1 / 2) * (1 - p) ^ (((k : ℝ) - 1) / 2)) *
        (q ^ ((n : ℝ) - 1 / 2) * (1 - q) ^ (((k : ℝ) - 1) / 2))
    have hFq_sum : ∀ q ∈ Ioo (0 : ℝ) 1, HasSum (fun n => Fq n q) (G p q) := by
      intro q hq
      have hq0 : 0 < q := hq.1
      have hpqt0 : 0 ≤ p * q * t ^ 2 := by positivity
      have hpqt1 : p * q * t ^ 2 < 1 := by
        have : p * q < 1 := by nlinarith [hp.2, hq.2]
        nlinarith [mul_nonneg hp0.le hq0.le]
      have hser := (hasSum_one_div_one_sub_rpow (c := c) hpqt0 hpqt1).mul_left
        (p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2) *
          (q ^ (-(1 / 2 : ℝ)) * (1 - q) ^ (((k : ℝ) - 1) / 2)))
      refine hser.congr_fun fun n => ?_
      dsimp only [Fq]
      have hpn : p ^ (-(1 / 2 : ℝ)) * p ^ n = p ^ ((n : ℝ) - 1 / 2) := by
        rw [← Real.rpow_natCast p n, ← Real.rpow_add hp0]; congr 1; ring
      have hqn : q ^ (-(1 / 2 : ℝ)) * q ^ n = q ^ ((n : ℝ) - 1 / 2) := by
        rw [← Real.rpow_natCast q n, ← Real.rpow_add hq0]; congr 1; ring
      rw [mul_pow, mul_pow]
      symm
      calc p ^ (-(1 / 2 : ℝ)) * (1 - p) ^ (((k : ℝ) - 1) / 2) *
              (q ^ (-(1 / 2 : ℝ)) * (1 - q) ^ (((k : ℝ) - 1) / 2)) *
              ((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c * (p ^ n * q ^ n * (t ^ 2) ^ n))
          = ((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c * (t ^ 2) ^ n) *
              ((p ^ (-(1 / 2 : ℝ)) * p ^ n) * (1 - p) ^ (((k : ℝ) - 1) / 2)) *
              ((q ^ (-(1 / 2 : ℝ)) * q ^ n) * (1 - q) ^ (((k : ℝ) - 1) / 2)) := by ring
        _ = _ := by rw [hpn, hqn]
    have hFq_nn : ∀ n, ∀ q ∈ Ioo (0 : ℝ) 1, 0 ≤ Fq n q := by
      intro n q hq
      have hq0 : 0 < q := hq.1
      have hq1 : 0 < 1 - q := by linarith [hq.2]
      have hpoch := ascPochhammer_eval_pos hc_pos n
      dsimp only [Fq]
      positivity
    have htsum_q := h_nonneg_tsum_int Fq (G p)
      (fun n => by dsimp only [Fq]; fun_prop) hFq_nn hFq_sum hGp_int
    have hterm_q : ∀ n : ℕ, (∫ q in Ioo (0 : ℝ) 1, Fq n q) =
        ((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c * (t ^ 2) ^ n * Bval n) *
          (p ^ ((n : ℝ) - 1 / 2) * (1 - p) ^ (((k : ℝ) - 1) / 2)) := by
      intro n
      dsimp only [Fq]
      rw [integral_const_mul, hbeta_eval n]
      ring
    -- Also need Summable to turn tsum_eq into HasSum!
    have hsumm : Summable (fun n : ℕ => ∫ q in Ioo (0 : ℝ) 1, Fq n q) := by
      have h1 : (∑' n, ∫⁻ q, ‖Fq n q‖ₑ ∂μ01) ≠ ⊤ := by
        rw [← lintegral_tsum fun n => (by dsimp only [Fq]; fun_prop : Measurable (Fq n)).enorm.aemeasurable]
        have h2 : ∀ᵐ q ∂μ01, (∑' n, ‖Fq n q‖ₑ) = ‖G p q‖ₑ := by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
          have hF_enorm : ∀ n, ‖Fq n q‖ₑ = ENNReal.ofReal (Fq n q) := fun n =>
            Real.enorm_eq_ofReal (hFq_nn n q hq)
          have hS_enorm : ‖G p q‖ₑ = ENNReal.ofReal (G p q) :=
            Real.enorm_eq_ofReal ((hFq_sum q hq).nonneg (fun n => hFq_nn n q hq))
          simp_rw [hF_enorm, hS_enorm]
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hFq_nn n q hq) (hFq_sum q hq).summable,
            (hFq_sum q hq).tsum_eq]
        rw [lintegral_congr_ae h2]
        exact hGp_int.2.ne
      have hnn : ∀ n, 0 ≤ ∫ q in Ioo (0 : ℝ) 1, Fq n q := fun n =>
        setIntegral_nonneg measurableSet_Ioo (fun q hq => hFq_nn n q hq)
      have heq_enorm : ∀ n, ENNReal.ofReal (∫ q in Ioo (0 : ℝ) 1, Fq n q) = ∫⁻ q, ‖Fq n q‖ₑ ∂μ01 := by
        intro n
        have hbeta_n : IntegrableOn (fun q : ℝ => q ^ ((n : ℝ) - 1 / 2) * (1 - q) ^ (((k : ℝ) - 1) / 2))
            (Ioo 0 1) volume := by
          have h := integrableOn_beta_Ioo (u := (n : ℝ) + 1 / 2) (v := ((k : ℝ) + 1) / 2)
            (by positivity) (by positivity)
          have h1' : (n : ℝ) + 1 / 2 - 1 = (n : ℝ) - 1 / 2 := by ring
          have h2' : ((k : ℝ) + 1) / 2 - 1 = ((k : ℝ) - 1) / 2 := by ring
          rwa [h1', h2'] at h
        have hint : IntegrableOn (Fq n) (Ioo 0 1) volume :=
          hbeta_n.const_mul
            (((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c * (t ^ 2) ^ n) *
              (p ^ ((n : ℝ) - 1 / 2) * (1 - p) ^ (((k : ℝ) - 1) / 2)))
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq using hFq_nn n q hq)]
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
        exact (Real.enorm_eq_ofReal (hFq_nn n q hq)).symm
      let a : ℕ → ℝ≥0 := fun n => ⟨∫ q in Ioo (0 : ℝ) 1, Fq n q, hnn n⟩
      have ha_ne_top : (∑' n, (a n : ℝ≥0∞)) ≠ ∞ := by
        have hcoe : ∀ n, (a n : ℝ≥0∞) = ENNReal.ofReal (∫ q in Ioo (0 : ℝ) 1, Fq n q) := fun n => by
          rw [ENNReal.ofReal_eq_coe_nnreal (hnn n)]; rfl
        simp_rw [hcoe, heq_enorm]
        exact h1
      exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp ha_ne_top)
    have hhs := hsumm.hasSum
    rw [← htsum_q] at hhs
    exact hhs.congr_fun (fun n => (hterm_q n).symm)
  -- Step E2: Integrate term-by-term over p ∈ Ioo 0 1
  let Fp : ℕ → ℝ → ℝ := fun n p =>
    ((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c * (t ^ 2) ^ n * Bval n) *
      (p ^ ((n : ℝ) - 1 / 2) * (1 - p) ^ (((k : ℝ) - 1) / 2))
  have hBval_nn : ∀ n, 0 ≤ Bval n := fun n => by
    dsimp only [Bval]
    have h1 := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1 / 2)
    have h2 := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < ((k : ℝ) + 1) / 2)
    have h3 := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < c + n)
    positivity
  have hFp_nn : ∀ n, ∀ p ∈ Ioo (0 : ℝ) 1, 0 ≤ Fp n p := by
    intro n p hp
    have hp0 : 0 < p := hp.1
    have hp1 : 0 < 1 - p := by linarith [hp.2]
    have hpoch := ascPochhammer_eval_pos hc_pos n
    have hB := hBval_nn n
    dsimp only [Fp]
    positivity
  have hp_tsum := h_nonneg_tsum_int Fp (fun p => ∫ q in Ioo (0 : ℝ) 1, G p q)
    (fun n => by dsimp only [Fp]; fun_prop) hFp_nn hq_expand houter_int
  -- Step F: Simplify each term to match F k t
  rw [hcov_iter, hp_tsum]
  have hterm_p : ∀ n : ℕ,
      (∫ p in Ioo (0 : ℝ) 1, Fp n p) =
        (n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval c * (t ^ 2) ^ n * (Bval n) ^ 2 := by
    intro n
    dsimp only [Fp]
    rw [integral_const_mul, hbeta_eval n]
    ring
  simp_rw [hterm_p]
  rw [← tsum_mul_left, ← tsum_mul_left]
  unfold F
  rw [ordinaryHypergeometric_eq_tsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  -- Algebraic simplification of the n-th term using Gamma_add_nat
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hG_half : Real.Gamma ((n : ℝ) + 1 / 2) =
      (ascPochhammer ℝ n).eval (1 / 2 : ℝ) * Real.sqrt π := by
    rw [add_comm, gamma_add_nat (by norm_num : (0 : ℝ) < 1 / 2) n, Real.Gamma_one_half_eq]
  have hG_c : Real.Gamma (c + n) =
      (ascPochhammer ℝ n).eval c * (((k : ℝ) / 2) * Real.Gamma ((k : ℝ) / 2)) := by
    rw [gamma_add_nat hc_pos n]
    congr 1
    dsimp only [c]
    exact Real.Gamma_add_one (by positivity)
  have hB_simp : (Bval n) ^ 2 =
      ((ascPochhammer ℝ n).eval (1 / 2 : ℝ)) ^ 2 * π * (Real.Gamma (((k : ℝ) + 1) / 2)) ^ 2 /
        (((ascPochhammer ℝ n).eval c) ^ 2 * ((k : ℝ) / 2) ^ 2 * (Real.Gamma ((k : ℝ) / 2)) ^ 2) := by
    dsimp only [Bval]
    rw [hG_half, hG_c, div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  have hpoch_c_ne : (ascPochhammer ℝ n).eval c ≠ 0 := (ascPochhammer_eval_pos hc_pos n).ne'
  have hGk_ne : Real.Gamma ((k : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hpi_ne : (π : ℝ) ≠ 0 := Real.pi_pos.ne'
  have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
  rw [hB_simp, smul_eq_mul]
  dsimp only [c]
  field_simp

end Lemma4Aux

theorem solution {k d : ℕ} (hk : 1 ≤ k)
    (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Fin k → Fin d → Ω → ℝ) (hR : IsStdGaussianMatrix P R) :
    (∫ ω, inner ℝ (unitVec (gaussianProject R ω u))
      (unitVec (gaussianProject R ω v)) ∂P) = F k (inner ℝ u v) := by
  set t := inner ℝ u v
  set s := Real.sqrt (1 - t ^ 2)
  have ht_le : t ^ 2 ≤ 1 := by
    have habs : |t| ≤ 1 := by simpa [t, hu, hv] using abs_real_inner_le_norm u v
    nlinarith [abs_le.mp habs]
  have hts : t ^ 2 + s ^ 2 = 1 := by
    dsimp only [s]; rw [Real.sq_sqrt (by linarith)]; ring
  let f : (Fin k → ℝ × ℝ) → ℝ := fun w =>
    inner ℝ (unitVec (WithLp.toLp 2 (fun a : Fin k => (w a).1)))
      (unitVec (WithLp.toLp 2 (fun a : Fin k => (w a).2)))
  have hf_meas : Measurable f := by
    dsimp only [f, unitVec]
    have h1 : Measurable (fun w : Fin k → ℝ × ℝ => WithLp.toLp 2 (fun a : Fin k => (w a).1)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).measurable.comp
        (measurable_pi_lambda _ fun a => measurable_fst.comp (measurable_pi_apply a))
    have h2 : Measurable (fun w : Fin k → ℝ × ℝ => WithLp.toLp 2 (fun a : Fin k => (w a).2)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).measurable.comp
        (measurable_pi_lambda _ fun a => measurable_snd.comp (measurable_pi_apply a))
    have h1' : Measurable (fun w : Fin k → ℝ × ℝ =>
        ‖WithLp.toLp 2 (fun a : Fin k => (w a).1)‖⁻¹ • WithLp.toLp 2 (fun a : Fin k => (w a).1)) :=
      (continuous_norm.measurable.comp h1).inv.smul h1
    have h2' : Measurable (fun w : Fin k → ℝ × ℝ =>
        ‖WithLp.toLp 2 (fun a : Fin k => (w a).2)‖⁻¹ • WithLp.toLp 2 (fun a : Fin k => (w a).2)) :=
      (continuous_norm.measurable.comp h2).inv.smul h2
    exact continuous_inner.measurable.comp (h1'.prodMk h2')
  have hR_meas : ∀ a c, Measurable (fun ω => R a c ω) := fun a c => by
    have h := hR.1 (finProdFinEquiv (a, c))
    convert h using 1
    ext ω
    simp only [Equiv.symm_apply_apply]
  have hproj_meas : Measurable (fun ω (a : Fin k) =>
      (∑ c : Fin d, R a c ω * u c, ∑ c : Fin d, R a c ω * v c)) := by
    refine measurable_pi_lambda _ fun a => Measurable.prodMk ?_ ?_
    · exact Finset.measurable_sum _ fun c _ => (hR_meas a c).mul_const (u c)
    · exact Finset.measurable_sum _ fun c _ => (hR_meas a c).mul_const (v c)
  have hlin_meas : Measurable (fun (w : Fin k → ℝ × ℝ) (a : Fin k) =>
      ((w a).1, t * (w a).1 + s * (w a).2)) := by
    refine measurable_pi_lambda _ fun a => by fun_prop
  have hlaw := Lemma4Aux.law_proj_eq u v hu hv P R hR
  calc (∫ ω, inner ℝ (unitVec (gaussianProject R ω u))
          (unitVec (gaussianProject R ω v)) ∂P)
      = ∫ ω, f (fun a => (∑ c : Fin d, R a c ω * u c, ∑ c : Fin d, R a c ω * v c)) ∂P := by
        rfl
    _ = ∫ w, f w ∂(P.map (fun ω a =>
          (∑ c : Fin d, R a c ω * u c, ∑ c : Fin d, R a c ω * v c))) :=
        (integral_map hproj_meas.aemeasurable hf_meas.aestronglyMeasurable).symm
    _ = ∫ w, f w ∂((Lemma4Aux.stdGaussK k).map (fun w a =>
          ((w a).1, t * (w a).1 + s * (w a).2))) := by
        rw [hlaw]
    _ = ∫ w, f (fun a => ((w a).1, t * (w a).1 + s * (w a).2)) ∂(Lemma4Aux.stdGaussK k) :=
        integral_map hlin_meas.aemeasurable hf_meas.aestronglyMeasurable
    _ = F k t := Lemma4Aux.main_model_eq hk hts
