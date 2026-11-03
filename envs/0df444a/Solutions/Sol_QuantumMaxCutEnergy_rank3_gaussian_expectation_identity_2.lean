-- Prove2me | solution 2 for QuantumMaxCutEnergy.rank3_gaussian_expectation_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T22:39:43.288643+00:00
-- url     : https://prove2.me/submissions/a5f7e9c1-b3fc-4636-81fe-5eff373ff271

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

noncomputable section
namespace Rank3Gaussian

abbrev γ2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

abbrev μ3 : Measure (Fin 3 → ℝ × ℝ) := Measure.pi (fun _ : Fin 3 => γ2)

def Dbloch (r q c : ℝ) : ℝ := (1 + 2*r^2)*(1 + 2*q^2) - 4*c^2*r^2*q^2

noncomputable def bovInt (c : ℝ) : ℝ :=
  (12*c/Real.pi) * ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ),
    (Dbloch r q c) ^ (-(5/2) : ℝ)

def nrm3 (x : Fin 3 → ℝ) : ℝ := Real.sqrt (∑ a, (x a)^2)

def innerQ (x z : Fin 3 → ℝ) : ℝ :=
  if nrm3 x = 0 ∨ nrm3 z = 0 then 0 else (∑ a, x a * z a)/(nrm3 x * nrm3 z)

def zcoord (c s : ℝ) (p : Fin 3 → ℝ × ℝ) (a : Fin 3) : ℝ := c*(p a).1 + s*(p a).2

def psiMat (c s : ℝ) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ :=
  Matrix.of fun (a, p) (b, q) =>
    if a = b then (if p = 0 ∧ q = 0 then 1
      else if p = 1 ∧ q = 0 then c
      else if p = 1 ∧ q = 1 then s else 0) else 0

def phiMat {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin n) ℝ :=
  Matrix.of fun (a, p) (b, k) =>
    if a = b then (if p = 0 then u k else 0) + (if p = 1 then v k else 0) else 0

end Rank3Gaussian
end

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
open Filter

noncomputable section
namespace Rank3Gaussian

theorem integral_sq_gauss : ∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

theorem integral_sq_mulGauss : ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
  have h := integral_sq_gauss
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)] at h
  simp only [smul_eq_mul, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero] at h
  have h2 : ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * x ^ 2
      = (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ 2 * Real.exp (-x ^ 2 / 2)) := by
    intro x
    ring
  simp_rw [h2] at h
  rw [integral_const_mul] at h
  have hne : Real.sqrt (2 * Real.pi) ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
  have h3 := congrArg (fun t => Real.sqrt (2 * Real.pi) * t) h
  rw [mul_inv_cancel_left₀ hne, mul_one] at h3
  exact h3

theorem integral_sq_exp_neg_sq (α : ℝ) (hα : 0 < α) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-α * x ^ 2 / 2) = Real.sqrt (2 * Real.pi) / (α * Real.sqrt α) := by
  have hs := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure ℝ))
      (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2 / 2)) (Real.sqrt α)
  simp only [Module.finrank_self, pow_one] at hs
  rw [abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg α)), smul_eq_mul] at hs
  have hfg : ∀ x : ℝ, (Real.sqrt α • x) ^ 2 * Real.exp (-(Real.sqrt α • x) ^ 2 / 2)
      = α * (x ^ 2 * Real.exp (-α * x ^ 2 / 2)) := by
    intro x
    rw [smul_eq_mul, mul_pow, Real.sq_sqrt (le_of_lt hα)]
    ring_nf
  simp_rw [hfg] at hs
  simp only [integral_const_mul] at hs
  rw [integral_sq_mulGauss] at hs
  field_simp [hα.ne', Real.sqrt_ne_zero'.2 hα, Real.sqrt_nonneg α] at hs ⊢
  linarith [hs]

theorem integral_sq_exp_neg_sq_mul (a : ℝ) (ha : -(1 / 2 : ℝ) < a) :
    ∫ t : ℝ, t ^ 2 * Real.exp (-a * t ^ 2) ∂(gaussianReal 0 1)
      = Real.sqrt ((1 + 2 * a)⁻¹) ^ 3 := by
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  have hα : (0 : ℝ) < 1 + 2 * a := by linarith
  have hpt : ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp (-x ^ 2 / 2) * (x ^ 2 * Real.exp (-a * x ^ 2))
      = (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ 2 * Real.exp (-(1 + 2 * a) * x ^ 2 / 2)) := by
    intro x
    rw [show -(1 + 2 * a) * x ^ 2 / 2 = -x ^ 2 / 2 + -a * x ^ 2 from by ring, Real.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sq_exp_neg_sq (1 + 2 * a) hα]
  have hsqrt3 : Real.sqrt ((1 + 2 * a)⁻¹) ^ 3 = 1/((1 + 2 * a) * Real.sqrt (1 + 2 * a)) := by
    rw [show (Real.sqrt ((1 + 2 * a)⁻¹)) ^ 3 = (Real.sqrt ((1 + 2 * a)⁻¹)) ^ 2
          * Real.sqrt ((1 + 2 * a)⁻¹) from by ring,
      Real.sq_sqrt (inv_nonneg.2 hα.le), Real.sqrt_inv]
    rw [← mul_inv, ← one_div]
  rw [show (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi) / ((1 + 2 * a) * Real.sqrt (1 + 2 * a)))
      = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi)) / ((1 + 2 * a) * Real.sqrt (1 + 2 * a)) from by
        rw [← mul_div_assoc]]
  rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by positivity : (0:ℝ) < 2 * Real.pi)), hsqrt3]

theorem integral_mul_exp_neg_mul_sq_Ioi {b : ℝ} (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have hb2 : (0 : ℝ) < 2 * b := by linarith
  have hx2 : (2 * b) ≠ 0 := ne_of_gt hb2
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2)) (x * Real.exp (-b * x ^ 2)) x := by
    intro x hx
    have h1 := ((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)
    have eqq : -(2 * b)⁻¹ * (Real.exp (-b * x ^ 2) * (-b * (2 * x))) = x * Real.exp (-b * x ^ 2) := by
      calc -(2 * b)⁻¹ * (Real.exp (-b * x ^ 2) * (-b * (2 * x)))
          = (((2 * b)⁻¹ * (2 * b)) * x) * Real.exp (-b * x ^ 2) := by ring
        _ = (1 * x) * Real.exp (-b * x ^ 2) := by rw [inv_mul_cancel₀ hx2]
        _ = x * Real.exp (-b * x ^ 2) := by ring
    rw [← eqq]
    refine h1.congr_deriv ?_
    norm_num [pow_one]
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-b * x ^ 2)) (Set.Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq hb).integrableOn
  have htop2 : Filter.Tendsto (fun y : ℝ => b * y ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hb (Filter.tendsto_pow_atTop two_ne_zero)
  have htopF : Filter.Tendsto (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2)) atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    have heq : (fun y : ℝ => Real.exp (-b * y ^ 2)) = fun y => Real.exp (-(b * y ^ 2)) := by
      funext y
      congr 1
      ring
    have h2 : Filter.Tendsto (fun y : ℝ => Real.exp (-b * y ^ 2)) atTop (𝓝 0) := by
      rw [heq]
      exact (Real.tendsto_exp_neg_atTop_nhds_zero).comp htop2
    exact Filter.Tendsto.const_mul (-(2 * b)⁻¹) h2
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htopF
  have h0 : (-(2 * b)⁻¹ * Real.exp (-b * (0 : ℝ) ^ 2)) = -(2 * b)⁻¹ := by
    simp [pow_two, mul_zero, Real.exp_zero, mul_one]
  rw [mul_zero, h0, zero_sub, neg_neg] at hmain
  exact hmain

theorem integral_mul_exp_neg_mul_sq_Iic {b : ℝ} (hb : 0 < b) :
    ∫ x in Set.Iic (0 : ℝ), x * Real.exp (-b * x ^ 2) = -(2 * b)⁻¹ := by
  have hI := integral_mul_exp_neg_mul_sq_Ioi hb
  have key : ∫ x in Set.Iic (0 : ℝ), (fun y => -(y * Real.exp (-b * y ^ 2))) (-x)
      = ∫ y in Set.Ici (0 : ℝ), -(y * Real.exp (-b * y ^ 2)) := by
    have A : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hm := MeasurableEmbedding.setIntegral_map (μ := volume) A
        (fun y => -(y * Real.exp (-b * y ^ 2))) (Set.Ici (0 : ℝ))
    rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at hm
    rw [show ((fun x : ℝ => -x) ⁻¹' Set.Ici (0 : ℝ)) = Set.Iic (0 : ℝ) from by ext x; simp] at hm
    exact hm.symm
  rw [show (∫ x in Set.Iic (0 : ℝ), x * Real.exp (-b * x ^ 2))
      = ∫ x in Set.Iic (0 : ℝ), (fun y => -(y * Real.exp (-b * y ^ 2))) (-x) from by
      refine setIntegral_congr_fun measurableSet_Iic fun x hx => by
        simp]
  rw [key, integral_neg]
  rw [integral_Ici_eq_integral_Ioi, hI]

theorem integral_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x * Real.exp (-b * x ^ 2) = 0 := by
  have hI : Integrable fun x : ℝ => x * Real.exp (-b * x ^ 2) := integrable_mul_exp_neg_mul_sq hb
  have hsplit := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hI
  rw [Set.compl_Ioi] at hsplit
  rw [← hsplit, integral_mul_exp_neg_mul_sq_Ioi hb, integral_mul_exp_neg_mul_sq_Iic hb]
  ring

theorem integral_exp_neg_sq_add_mul (a b : ℝ) (ha : -(1 / 2 : ℝ) < a) :
    ∫ t : ℝ, Real.exp (-a * t ^ 2 - b * t) ∂(gaussianReal 0 1)
      = Real.sqrt ((1 + 2 * a)⁻¹) * Real.exp (b ^ 2 / (2 * (1 + 2 * a))) := by
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  have hα : (0 : ℝ) < 1 + 2 * a := by linarith
  obtain ⟨b0, hb0, hbdef⟩ : ∃ b0 : ℝ, 0 < b0 ∧ (1 + 2 * a) / 2 = b0 :=
    ⟨(1 + 2 * a) / 2, by linarith, rfl⟩
  set m := -b / (1 + 2 * a) with hm
  have hp2 : ∀ x : ℝ, -x ^ 2 / 2 + (-a * x ^ 2 - b * x)
      = b ^ 2 / (2 * (1 + 2 * a)) + (-(1 + 2 * a) * (x - m) ^ 2 / 2) := by
    intro x
    rw [hm]
    field_simp [hα.ne']
    ring
  have hpt : ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp (-x ^ 2 / 2) * Real.exp (-a * x ^ 2 - b * x)
      = Real.exp (b ^ 2 / (2 * (1 + 2 * a))) * (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp (-(1 + 2 * a) * (x - m) ^ 2 / 2) := by
    intro x
    rw [show (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-a * x ^ 2 - b * x)
        = (√(2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * Real.exp (-a * x ^ 2 - b * x)) from by ring]
    rw [← Real.exp_add, hp2 x, Real.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hrs : (fun x : ℝ => Real.exp (-(1 + 2 * a) * (x - m) ^ 2 / 2))
      = fun x : ℝ => (fun y : ℝ => Real.exp (-(1 + 2 * a) * y ^ 2 / 2)) (x - m) := by
    funext x
    simp
  rw [hrs, integral_sub_right_eq_self (μ := volume)
      (fun y : ℝ => Real.exp (-(1 + 2 * a) * y ^ 2 / 2)) m]
  have hset : ∀ x : ℝ, -(1 + 2 * a) * x ^ 2 / 2 = -b0 * x ^ 2 := by
    intro x
    rw [← hbdef]
    ring
  simp_rw [hset, integral_gaussian b0]
  rw [← hbdef]
  rw [show Real.pi / ((1 + 2 * a) / 2) = (2 * Real.pi) * (1 + 2 * a)⁻¹ from by
    field_simp [hα.ne']]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) ((1 + 2 * a)⁻¹)]
  rw [show Real.exp (b ^ 2 / (2 * (1 + 2 * a))) * (√(2 * Real.pi))⁻¹ * (√(2 * Real.pi) * √(1 + 2 * a)⁻¹)
      = (Real.exp (b ^ 2 / (2 * (1 + 2 * a))) * √(1 + 2 * a)⁻¹)
        * ((√(2 * Real.pi))⁻¹ * √(2 * Real.pi)) from by ring]
  rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < 2 * Real.pi)), mul_one]
  ring

theorem integral_mul_exp_neg_sq_add_mul (a b : ℝ) (ha : -(1 / 2 : ℝ) < a) :
    ∫ t : ℝ, t * Real.exp (-a * t ^ 2 - b * t) ∂(gaussianReal 0 1)
      = -b * (Real.sqrt ((1 + 2 * a)⁻¹)) ^ 3 * Real.exp (b ^ 2 / (2 * (1 + 2 * a))) := by
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  have hα : (0 : ℝ) < 1 + 2 * a := by linarith
  obtain ⟨b0, hb0, hbdef⟩ : ∃ b0 : ℝ, 0 < b0 ∧ (1 + 2 * a) / 2 = b0 :=
    ⟨(1 + 2 * a) / 2, by linarith, rfl⟩
  set m := -b / (1 + 2 * a) with hm
  have hp2 : ∀ x : ℝ, -x ^ 2 / 2 + (-a * x ^ 2 - b * x)
      = b ^ 2 / (2 * (1 + 2 * a)) + (-(1 + 2 * a) * (x - m) ^ 2 / 2) := by
    intro x
    rw [hm]
    field_simp [hα.ne']
    ring
  have hexp : ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
        * Real.exp (-a * x ^ 2 - b * x)
      = Real.exp (b ^ 2 / (2 * (1 + 2 * a))) * (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp (-(1 + 2 * a) * (x - m) ^ 2 / 2) := by
    intro x
    rw [show (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-a * x ^ 2 - b * x)
        = (√(2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * Real.exp (-a * x ^ 2 - b * x)) from by ring]
    rw [← Real.exp_add, hp2 x, Real.exp_add]
    ring
  have hpt : ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp (-x ^ 2 / 2) * (x * Real.exp (-a * x ^ 2 - b * x))
      = (Real.exp (b ^ 2 / (2 * (1 + 2 * a))) * (Real.sqrt (2 * Real.pi))⁻¹)
        * (x * Real.exp (-(1 + 2 * a) * (x - m) ^ 2 / 2)) := by
    intro x
    rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
          * (x * Real.exp (-a * x ^ 2 - b * x))
        = x * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
          * Real.exp (-a * x ^ 2 - b * x)) from by ring]
    rw [hexp x]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hrs' : (fun x : ℝ => x * Real.exp (-(1 + 2 * a) * (x - m) ^ 2 / 2))
      = fun x : ℝ => (fun y : ℝ => (y + m) * Real.exp (-(1 + 2 * a) * y ^ 2 / 2)) (x - m) := by
    funext x
    simp
  rw [hrs', integral_sub_right_eq_self (μ := volume)
      (fun y : ℝ => (y + m) * Real.exp (-(1 + 2 * a) * y ^ 2 / 2)) m]
  have hset : ∀ x : ℝ, -(1 + 2 * a) * x ^ 2 / 2 = -b0 * x ^ 2 := by
    intro x
    rw [← hbdef]
    ring
  simp_rw [hset]
  have hsplit : ∀ x : ℝ, (x + m) * Real.exp (-b0 * x ^ 2)
      = x * Real.exp (-b0 * x ^ 2) + m * Real.exp (-b0 * x ^ 2) := by
    intro x
    ring
  simp_rw [hsplit]
  rw [integral_add (integrable_mul_exp_neg_mul_sq hb0)
      ((integrable_exp_neg_mul_sq hb0).const_mul m)]
  rw [integral_mul_exp_neg_mul_sq hb0, integral_const_mul, integral_gaussian b0]
  rw [← hbdef]
  rw [show Real.pi / ((1 + 2 * a) / 2) = (2 * Real.pi) * (1 + 2 * a)⁻¹ from by
    field_simp [hα.ne']]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) ((1 + 2 * a)⁻¹)]
  rw [show Real.exp (b ^ 2 / (2 * (1 + 2 * a))) * (√(2 * Real.pi))⁻¹
        * (0 + m * (√(2 * Real.pi) * √(1 + 2 * a)⁻¹))
      = (Real.exp (b ^ 2 / (2 * (1 + 2 * a))) * m) * √(1 + 2 * a)⁻¹
        * ((√(2 * Real.pi))⁻¹ * √(2 * Real.pi)) from by ring]
  rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < 2 * Real.pi)), mul_one]
  rw [hm]
  rw [show (Real.sqrt ((1 + 2 * a)⁻¹)) ^ 3 = (1 + 2 * a)⁻¹ * Real.sqrt ((1 + 2 * a)⁻¹) from by
    rw [show ((Real.sqrt ((1 + 2 * a)⁻¹)) ^ 3) = ((Real.sqrt ((1 + 2 * a)⁻¹)) ^ 2)
          * Real.sqrt ((1 + 2 * a)⁻¹) from by ring,
      Real.sq_sqrt (inv_nonneg.2 hα.le)]]
  ring
end Rank3Gaussian
end

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology

noncomputable section
namespace Rank3Gaussian

theorem integral_exp_neg_sq_mul (a : ℝ) (ha : -(1 / 2 : ℝ) < a) :
    ∫ t : ℝ, Real.exp (-a * t ^ 2) ∂(gaussianReal 0 1)
      = Real.sqrt ((1 + 2 * a)⁻¹) := by
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  have hpt : ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-a * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a + 1 / 2) * x ^ 2) := by
    intro x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian]
  have hpos : (0 : ℝ) < 1 + 2 * a := by linarith
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have harg : Real.pi / (a + 1 / 2) = 2 * Real.pi / (1 + 2 * a) := by
    field_simp
    ring
  rw [harg, Real.sqrt_div' _ (le_of_lt hpos), ← Real.sqrt_inv]
  rw [← mul_div_assoc, ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2 * Real.pi)⁻¹),
    inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), Real.sqrt_one, one_div,
    ← Real.sqrt_inv]

theorem bivar_exp_factor (r q c s x y : ℝ) :
    Real.exp (-(r ^ 2 * x ^ 2) - q ^ 2 * (c * x + s * y) ^ 2)
      = Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem bivar_inner_k (q c s x : ℝ) :
    ∫ y : ℝ, Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y) ∂(gaussianReal 0 1)
      = Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
        * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2)))) := by
  have aq : -(1 / 2 : ℝ) < q ^ 2 * s ^ 2 := by nlinarith [sq_nonneg (q * s)]
  simpa using integral_exp_neg_sq_add_mul (q ^ 2 * s ^ 2) (2 * q ^ 2 * c * s * x) aq

theorem bivar_inner_kmul (q c s x : ℝ) :
    ∫ y : ℝ, y * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y) ∂(gaussianReal 0 1)
      = -(2 * q ^ 2 * c * s * x) * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)) ^ 3
        * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2)))) := by
  have aq : -(1 / 2 : ℝ) < q ^ 2 * s ^ 2 := by nlinarith [sq_nonneg (q * s)]
  simpa using integral_mul_exp_neg_sq_add_mul (q ^ 2 * s ^ 2) (2 * q ^ 2 * c * s * x) aq

theorem bivar_kernel_bound (q c s x y : ℝ) :
    Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)
      ≤ Real.exp (q ^ 2 * c ^ 2 * x ^ 2) := by
  rw [Real.exp_le_exp]
  nlinarith [sq_nonneg q, sq_nonneg (s * y + c * x)]

theorem bivar_laplace0 (r q c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2) (hr : 0 < r) :
    ∫ p : ℝ × ℝ, Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) := by
  classical
  have hβpos : (0 : ℝ) < 1 + 2 * (q ^ 2 * s ^ 2) := by positivity
  have hβne : (1 + 2 * (q ^ 2 * s ^ 2)) ≠ 0 := by nlinarith [hβpos]
  have hIF : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · have hmeas : Measurable fun p : ℝ × ℝ =>
          Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2) := by
        fun_prop
      exact hmeas.aestronglyMeasurable
    · filter_upwards with p
      have habs : ‖Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2)‖
          = Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2) :=
        abs_of_nonneg (Real.exp_nonneg _)
      rw [habs]
      calc Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2)
          ≤ Real.exp 0 := Real.exp_le_exp.mpr (by
            have h1 : (0:ℝ) ≤ r ^ 2 * p.1 ^ 2 := by positivity
            have h2 : (0:ℝ) ≤ q ^ 2 * (c * p.1 + s * p.2) ^ 2 := by positivity
            linarith)
        _ = 1 := Real.exp_zero
  have hEqual : (fun p : ℝ × ℝ =>
      Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2))
      = (fun p : ℝ × ℝ => Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2)) :=
    funext fun p => by
      simpa using bivar_exp_factor r q c s p.1 p.2
  rw [hEqual]
  rw [hEqual] at hIF
  rw [integral_prod _ hIF]
  have hinnerEval : ∀ x : ℝ, (∫ y : ℝ, Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)
        ∂(gaussianReal 0 1))
      = Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
        * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2)))) := by
    intro x
    exact bivar_inner_k (q) (c) (s) (x)
  have hOuter : ∀ x : ℝ, Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
          * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2)))))
      = Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
        * Real.exp (-(r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2))) * x ^ 2) := by
    intro x
    rw [show Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
          * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2)))))
      = Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
        * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
          * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2))))) from by ring]
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  
  simp_rw [integral_const_mul]
  simp_rw [hinnerEval, hOuter]
  rw [integral_const_mul]
  have hEEpos : (0 : ℝ) < r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2)) := by positivity
  rw [integral_exp_neg_sq_mul (r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2)))
      (by linarith : -(1 / 2 : ℝ) < r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2)))]
  
  set D : ℝ := (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2 with hD
  have hDbeta : (1 + 2 * (r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2))))
      = D / (1 + 2 * (q ^ 2 * s ^ 2)) := by
    rw [hD]
    field_simp
    rw [hssq]
    ring_nf
  rw [hDbeta]
  have hInv : ((D : ℝ) / (1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ = (1 + 2 * (q ^ 2 * s ^ 2)) * D⁻¹ := by
    rw [inv_div]
    ring
  rw [hInv, Real.sqrt_mul hβpos.le D⁻¹, Real.sqrt_inv]
  rw [← mul_assoc]
  rw [show (√(1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ * √(1 + 2 * (q ^ 2 * s ^ 2)) = 1 from
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 hβpos)]
  rw [one_mul]
end Rank3Gaussian
end

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology

noncomputable section
namespace Rank3Gaussian

theorem mul_exp_neg_le (t : ℝ) : t * Real.exp (-t) ≤ Real.exp (-1) := by
  rcases le_total 0 t with ht | ht
  · have h1 : t ≤ Real.exp (t - 1) := by
      have h := Real.add_one_le_exp (t - 1)
      linarith
    have hprod : t * Real.exp (1 - t) ≤ (1 : ℝ) := by
      calc t * Real.exp (1 - t) ≤ Real.exp (t - 1) * Real.exp (1 - t) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
        _ = Real.exp 0 := by rw [← Real.exp_add]; congr 1; ring
        _ = 1 := Real.exp_zero
    have h4 : t * Real.exp (-t) = (t * Real.exp (1 - t)) * (Real.exp 1)⁻¹ := by
      rw [show t * Real.exp (-t) = t * Real.exp ((1 - t) + (-1)) from by congr 1; ring,
        Real.exp_add, Real.exp_neg]
      ring
    rw [h4]
    calc (t * Real.exp (1 - t)) * (Real.exp 1)⁻¹ ≤ (1 : ℝ) * (Real.exp 1)⁻¹ :=
        mul_le_mul_of_nonneg_right hprod (inv_nonneg.2 (Real.exp_nonneg _))
      _ = Real.exp (-1) := by rw [one_mul, Real.exp_neg]
  · exact (mul_nonpos_of_nonpos_of_nonneg ht (Real.exp_nonneg _)).trans (Real.exp_nonneg _)

theorem mul_exp_neg_sq_le (u b : ℝ) (hu : 0 ≤ u) (hb : 0 < b) :
    u * Real.exp (-b * u ^ 2) ≤ Real.sqrt ((2 * b * Real.exp 1)⁻¹) := by
  have hsquare : (u * Real.exp (-b * u ^ 2)) ^ 2 = u ^ 2 * Real.exp (-(2 * b * u ^ 2)) := by
    rw [mul_pow,
      show (Real.exp (-b * u ^ 2)) ^ 2 = Real.exp (-b * u ^ 2) * Real.exp (-b * u ^ 2) from by ring,
      ← Real.exp_add]
    ring
  have hmul : ((u * Real.exp (-b * u ^ 2)) ^ 2) * (2 * b * Real.exp 1) ≤ 1 := by
    rw [hsquare]
    have hcomm : ((u ^ 2 * Real.exp (-(2 * b * u ^ 2))) * (2 * b * Real.exp 1))
        = ((2 * b * u ^ 2) * Real.exp (-(2 * b * u ^ 2))) * Real.exp 1 := by
      ring
    rw [hcomm]
    refine (mul_le_mul_of_nonneg_right (mul_exp_neg_le _) (Real.exp_nonneg _)).trans ?_
    rw [← Real.exp_add]
    norm_num
  have hsq : (u * Real.exp (-b * u ^ 2)) ^ 2 ≤ (2 * b * Real.exp 1)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * b * Real.exp 1)]
    · exact hmul
  have hnn : 0 ≤ u * Real.exp (-b * u ^ 2) := by positivity
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hsq

theorem cross_kernel_shift (q c s x y : ℝ) :
    Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)
      = Real.exp (q ^ 2 * c ^ 2 * x ^ 2) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrable_sq_exp_neg_mul_sq_b (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) (gaussianReal 0 1) := by
  have hbound : ∀ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) ≤ Real.exp (-1) / b := by
    intro x
    have h := mul_exp_neg_le (b * x ^ 2)
    rw [le_div_iff₀ hb]
    rw [show x ^ 2 * Real.exp (-b * x ^ 2) * b = b * x ^ 2 * Real.exp (-(b * x ^ 2)) from by ring]
    exact h
  exact Integrable.mono' (integrable_const (Real.exp (-1) / b))
    ((by continuity : Continuous fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)).measurable.aestronglyMeasurable)
    (by
      filter_upwards with x
      rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2 * Real.exp (-b * x ^ 2))]
      exact hbound x
    )

theorem cross_htriple (q c s x y : ℝ) (hq : 0 < q) :
    |(s * y) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)|
      ≤ Real.sqrt ((2 * q ^ 2 * Real.exp 1)⁻¹) + |c| * |x| := by
  have hu1 : |s * y + c * x| * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)
      ≤ Real.sqrt ((2 * q ^ 2 * Real.exp 1)⁻¹) := by
    have hu1' := mul_exp_neg_sq_le (|s * y + c * x|) (q ^ 2) (abs_nonneg _)
      (by positivity : (0:ℝ) < q ^ 2)
    rwa [sq_abs (s * y + c * x)] at hu1'
  have hu2 : Real.exp (-q ^ 2 * (s * y + c * x) ^ 2) ≤ (1 : ℝ) := by
    have h := Real.exp_le_exp.mpr (show -q ^ 2 * (s * y + c * x) ^ 2 ≤ 0 from by
      nlinarith [sq_nonneg q, sq_nonneg (s * y + c * x)])
    rwa [Real.exp_zero] at h
  have hsw_to : (s * y) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)
      = (s * y + c * x) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)
        - (c * x) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2) := by ring
  rw [hsw_to]
  calc |(s * y + c * x) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)
        - (c * x) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)|
      ≤ |(s * y + c * x) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)|
        + |(c * x) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)| := abs_sub _ _
    _ = |s * y + c * x| * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)
        + (|c| * |x|) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2) := by
          congr 1
          · rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
          · rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_mul c x]
    _ ≤ Real.sqrt (2 * q ^ 2 * Real.exp 1)⁻¹ + |c| * |x| := by
          have hb2 : (|c| * |x|) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2) ≤ |c| * |x| := by
            calc (|c| * |x|) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)
                ≤ (|c| * |x|) * 1 :=
                  mul_le_mul_of_nonneg_left hu2 (mul_nonneg (abs_nonneg c) (abs_nonneg x))
              _ = |c| * |x| := mul_one _
          exact add_le_add hu1 hb2

theorem cross_kmul_bound (q c s x y : ℝ) (hs : s ≠ 0) (hq : 0 < q) :
    |y * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)|
      ≤ Real.exp (q ^ 2 * c ^ 2 * x ^ 2)
        * ((1 : ℝ) / |s|) * (Real.sqrt (2 * q ^ 2 * Real.exp 1)⁻¹ + |c * x|) := by
  have hspos : (0 : ℝ) < |s| := abs_pos.mpr hs
  have htriple := cross_htriple q c s x y hq
  rw [cross_kernel_shift]
  simp_rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [show |y| * (Real.exp (q ^ 2 * c ^ 2 * x ^ 2) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2))
      = Real.exp (q ^ 2 * c ^ 2 * x ^ 2) * (|y| * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)) from by ring]
  have hcore : |y| * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)
      ≤ (√(2 * q ^ 2 * Real.exp 1)⁻¹ + |c| * |x|) / |s| := by
    rw [le_div_iff₀ hspos]
    calc |y| * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2) * |s|
        = |(s * y) * Real.exp (-q ^ 2 * (s * y + c * x) ^ 2)| := by
          rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_mul]
          ring
      _ ≤ √(2 * q ^ 2 * Real.exp 1)⁻¹ + |c| * |x| := htriple
  rw [show Real.exp (q ^ 2 * c ^ 2 * x ^ 2) * (1 / |s|) * (√(2 * q ^ 2 * Real.exp 1)⁻¹ + |c| * |x|)
      = Real.exp (q ^ 2 * c ^ 2 * x ^ 2) * ((√(2 * q ^ 2 * Real.exp 1)⁻¹ + |c| * |x|) / |s|) from by
        ring]
  exact mul_le_mul_of_nonneg_left hcore (Real.exp_nonneg _)
end Rank3Gaussian
end

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology

noncomputable section
namespace Rank3Gaussian

theorem cross_outer (A : ℝ) (r q c s : ℝ) (hr : 0 < r) :
    ∫ x : ℝ, x ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * (A * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2))))))
        ∂(gaussianReal 0 1)
      = A * Real.sqrt ((1 + 2 * (r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2))))⁻¹) ^ 3 := by
  have hmerge : ∀ x : ℝ, x ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
      * (A * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2))))))
      = A * (x ^ 2 * Real.exp (-(r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2))) * x ^ 2)) := by
    intro x
    rw [show x ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * (A * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2))))))
      = A * (x ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2)))))) from by ring]
    rw [← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [hmerge]
  rw [integral_const_mul]
  have hEEpos : (0 : ℝ) < r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2)) := by positivity
  rw [integral_sq_exp_neg_sq_mul _ (by linarith : -(1/2 : ℝ) < r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2)))]

theorem cross_F_le (r q c s x y : ℝ) :
    Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
      * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)
      ≤ Real.exp (-r ^ 2 * x ^ 2) := by
  calc Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)
      ≤ Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2) * Real.exp (q ^ 2 * c ^ 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left (bivar_kernel_bound q c s x y) (Real.exp_nonneg _)
    _ = Real.exp (-r ^ 2 * x ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem cross_T1_integrable (r q c s : ℝ) (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2)))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  have hbound : ∀ p : ℝ × ℝ, p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
      * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))
      ≤ Real.exp (-1) / r ^ 2 := by
    intro p
    have h1 : p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))
        ≤ p.1 ^ 2 * Real.exp (-r ^ 2 * p.1 ^ 2) :=
      mul_le_mul_of_nonneg_left (cross_F_le r q c s p.1 p.2) (sq_nonneg _)
    refine h1.trans ?_
    rw [le_div_iff₀ hr2]
    rw [show p.1 ^ 2 * Real.exp (-r ^ 2 * p.1 ^ 2) * r ^ 2
        = (r ^ 2 * p.1 ^ 2) * Real.exp (-(r ^ 2 * p.1 ^ 2)) from by ring]
    exact mul_exp_neg_le _
  exact Integrable.mono' (integrable_const (Real.exp (-1) / r ^ 2))
    ((by continuity : Continuous fun p : ℝ × ℝ => p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))).measurable.aestronglyMeasurable)
    (by
      filter_upwards with p
      rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2)))]
      exact hbound p
    )

theorem cross_T1_value (r q c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2) (hr : 0 < r) :
    ∫ p : ℝ × ℝ, p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
        * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
          / (1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ ^ 3 := by
  classical
  rw [integral_prod _ (cross_T1_integrable r q c s hr)]
  have hpt : ∀ x : ℝ, ∫ y : ℝ, x ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
      * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)) ∂(gaussianReal 0 1)
      = x ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
          * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2)))))) := by
    intro x
    rw [show (fun y : ℝ => x ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)))
      = (fun y : ℝ => (x ^ 2 * Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2))
        * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)) from
        funext fun y => by ring]
    rw [integral_const_mul, bivar_inner_k]
    ring
  simp_rw [hpt]
  have hmain := cross_outer (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)) r q c s hr
  rw [hmain]
  have hDbeta : (1 + 2 * (r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2))))
      = ((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
        / (1 + 2 * (q ^ 2 * s ^ 2)) := by
    field_simp
    rw [hssq]
    ring_nf
  rw [hDbeta]

theorem cross_sq_exp_bound (r : ℝ) (hr : 0 < r) (x : ℝ) :
    x ^ 2 * Real.exp (-r ^ 2 * x ^ 2) ≤ Real.exp (-1) / r ^ 2 := by
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  rw [le_div_iff₀ hr2]
  rw [show x ^ 2 * Real.exp (-r ^ 2 * x ^ 2) * r ^ 2
      = (r ^ 2 * x ^ 2) * Real.exp (-(r ^ 2 * x ^ 2)) from by ring]
  exact mul_exp_neg_le _

theorem cross_T2_integrable (r q c s : ℝ) (hr : 0 < r) (hq : 0 < q) (hs : s ≠ 0) :
    Integrable (fun p : ℝ × ℝ => p.1 * p.2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2)))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  have hspos : (0:ℝ) < |s| := abs_pos.mpr hs
  exact Integrable.mono'
    (integrable_const
      ((1/|s|) * (Real.sqrt ((2*(r^2)*Real.exp 1)⁻¹) * Real.sqrt ((2*q^2*Real.exp 1)⁻¹)
        + |c| * (Real.exp (-1) / r ^ 2))))
    ((by continuity : Continuous fun p : ℝ × ℝ => p.1 * p.2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))).measurable.aestronglyMeasurable)
    (by
      filter_upwards with p
      have habsx : |p.1| * |p.1| = p.1 ^ 2 := by rw [← sq, sq_abs]
      have hmerge : Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
          * Real.exp (q ^ 2 * c ^ 2 * p.1 ^ 2) = Real.exp (-r ^ 2 * p.1 ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Real.norm_eq_abs]
      calc |p.1 * p.2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
              * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))|
          = |p.1| * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
              * |p.2 * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2)|) := by
            rw [show p.1 * p.2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
                  * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))
                = Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
                  * (p.1 * (p.2 * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))) from by ring,
              abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
            ring
        _ ≤ |p.1| * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
              * (Real.exp (q ^ 2 * c ^ 2 * p.1 ^ 2) * (1/|s|)
                * (Real.sqrt ((2*q^2*Real.exp 1)⁻¹) + |c * p.1|))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (cross_kmul_bound q c s p.1 p.2 hs hq) (Real.exp_nonneg _))
              (abs_nonneg _)
        _ = (1/|s|) * (|p.1| * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
              * Real.exp (q ^ 2 * c ^ 2 * p.1 ^ 2)) * (Real.sqrt ((2*q^2*Real.exp 1)⁻¹) + |c * p.1|)) := by ring
        _ = (1/|s|) * (|p.1| * Real.exp (-r ^ 2 * p.1 ^ 2)
              * (Real.sqrt ((2*q^2*Real.exp 1)⁻¹) + |c * p.1|)) := by rw [hmerge]
        _ ≤ (1/|s|) * (Real.sqrt ((2*(r^2)*Real.exp 1)⁻¹) * Real.sqrt ((2*q^2*Real.exp 1)⁻¹)
              + |c| * (Real.exp (-1) / r ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 1/|s|)
            rw [mul_add]
            refine add_le_add ?_ ?_
            · refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
              have hA1 : |p.1| * Real.exp (-r ^ 2 * p.1 ^ 2)
                  ≤ Real.sqrt ((2*(r^2)*Real.exp 1)⁻¹) := by
                have hA1' := mul_exp_neg_sq_le (|p.1|) (r ^ 2) (abs_nonneg p.1)
                  (by positivity : (0:ℝ) < r ^ 2)
                rwa [sq_abs] at hA1'
              exact hA1
            · rw [show |p.1| * Real.exp (-r ^ 2 * p.1 ^ 2) * |c * p.1|
                  = |c| * (p.1 ^ 2 * Real.exp (-r ^ 2 * p.1 ^ 2)) from by
                rw [abs_mul,
                  show |p.1| * Real.exp (-r ^ 2 * p.1 ^ 2) * (|c| * |p.1|)
                    = |c| * ((|p.1| * |p.1|) * Real.exp (-r ^ 2 * p.1 ^ 2)) from by ring,
                  habsx]]
              exact mul_le_mul_of_nonneg_left (cross_sq_exp_bound r hr p.1) (abs_nonneg _)
    )

theorem cross_T2_value (r q c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2) (hr : 0 < r) (hq : 0 < q) (hs : s ≠ 0) :
    ∫ p : ℝ × ℝ, p.1 * p.2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = (-(2 * q ^ 2 * c * s)) * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)) ^ 3
        * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
          / (1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ ^ 3 := by
  classical
  rw [integral_prod _ (cross_T2_integrable r q c s hr hq hs)]
  have hpt : ∀ x : ℝ, ∫ y : ℝ, x * y * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
      * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)) ∂(gaussianReal 0 1)
      = x ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * ((-(2 * q ^ 2 * c * s)) * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)) ^ 3
          * Real.exp ((2 * q ^ 2 * c * s * x) ^ 2 / (2 * (1 + 2 * (q ^ 2 * s ^ 2)))))) := by
    intro x
    rw [show (fun y : ℝ => x * y * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2)
        * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y)))
      = (fun y : ℝ => (x * Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * x ^ 2))
        * (y * Real.exp (-(q ^ 2 * s ^ 2) * y ^ 2 - (2 * q ^ 2 * c * s * x) * y))) from
        funext fun y => by ring]
    rw [integral_const_mul, bivar_inner_kmul]
    ring
  simp_rw [hpt]
  have hmain := cross_outer ((-(2 * q ^ 2 * c * s)) * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)) ^ 3) r q c s hr
  rw [hmain]
  have hDbeta : (1 + 2 * (r ^ 2 + q ^ 2 * c ^ 2 / (1 + 2 * (q ^ 2 * s ^ 2))))
      = ((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
        / (1 + 2 * (q ^ 2 * s ^ 2)) := by
    field_simp
    rw [hssq]
    ring_nf
  rw [hDbeta]

theorem sqrt_cube_split {β D : ℝ} (hβ : 0 < β) (hD : 0 < D) :
    Real.sqrt (β⁻¹) * Real.sqrt ((D/β)⁻¹) ^ 3 = β * Real.sqrt (D⁻¹) ^ 3 := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have h1 : β⁻¹ * (D/β)⁻¹ = D⁻¹ := by
    rw [inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hβne, one_mul]
  have hdiff : Real.sqrt (β⁻¹) * Real.sqrt ((D/β)⁻¹) = Real.sqrt (D⁻¹) := by
    rw [← Real.sqrt_mul (inv_nonneg.2 hβ.le), h1]
  have ht2 : (D/β)⁻¹ = β * D⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have ht_nonneg : (0:ℝ) ≤ (D/β)⁻¹ := inv_nonneg.2 (div_nonneg hD.le hβ.le)
  have hcube : (√((D/β)⁻¹)) ^ 3 = (D/β)⁻¹ * √((D/β)⁻¹) := by
    rw [show (√((D/β)⁻¹)) ^ 3 = (√((D/β)⁻¹)) ^ 2 * √((D/β)⁻¹) from by ring, Real.sq_sqrt ht_nonneg]
  have hcube2 : (√(D⁻¹)) ^ 3 = D⁻¹ * √(D⁻¹) := by
    rw [show (√(D⁻¹)) ^ 3 = (√(D⁻¹)) ^ 2 * √(D⁻¹) from by ring, Real.sq_sqrt (inv_nonneg.2 hD.le)]
  calc √((β:ℝ)⁻¹) * (√((D/β)⁻¹)) ^ 3
      = √((β:ℝ)⁻¹) * ((D/β)⁻¹ * √((D/β)⁻¹)) := by rw [hcube]
    _ = (D/β)⁻¹ * (√((β:ℝ)⁻¹) * √((D/β)⁻¹)) := by ring
    _ = (D/β)⁻¹ * √(D⁻¹) := by rw [hdiff]
    _ = β * D⁻¹ * √(D⁻¹) := by rw [ht2]
    _ = β * (√(D⁻¹)) ^ 3 := by rw [hcube2]; ring

theorem sqrt_cube_split' {β D : ℝ} (hβ : 0 < β) (hD : 0 < D) :
    Real.sqrt (β⁻¹) ^ 3 * Real.sqrt ((D/β)⁻¹) ^ 3 = Real.sqrt (D⁻¹) ^ 3 := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have h1 : β⁻¹ * (D/β)⁻¹ = D⁻¹ := by
    rw [inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hβne, one_mul]
  have hdiff : Real.sqrt (β⁻¹) * Real.sqrt ((D/β)⁻¹) = Real.sqrt (D⁻¹) := by
    rw [← Real.sqrt_mul (inv_nonneg.2 hβ.le), h1]
  rw [← mul_pow, hdiff]

theorem cross_tail (r q c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2) (hr : 0 < r) :
    c * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
        * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
          / (1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ ^ 3)
      + s * ((-(2 * q ^ 2 * c * s)) * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)) ^ 3
        * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
          / (1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ ^ 3)
    = c * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3 := by
  have hβpos : (0:ℝ) < 1 + 2 * (q ^ 2 * s ^ 2) := by positivity
  have hDpos : (0:ℝ) < (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2 := by
    have hform : (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2
        = 1 + 2 * r ^ 2 + 2 * q ^ 2 + 4 * r ^ 2 * q ^ 2 * s ^ 2 := by rw [hssq]; ring
    rw [hform]
    positivity
  have hA := sqrt_cube_split (β := 1 + 2 * (q ^ 2 * s ^ 2))
    (D := (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2) hβpos hDpos
  have hB := sqrt_cube_split' (β := 1 + 2 * (q ^ 2 * s ^ 2))
    (D := (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2) hβpos hDpos
  calc c * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)
          * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
            / (1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ ^ 3)
        + s * ((-(2 * q ^ 2 * c * s)) * (Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)) ^ 3
          * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
            / (1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ ^ 3)
      = c * ((1 + 2 * (q ^ 2 * s ^ 2))
          * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3)
        + (-(2 * q ^ 2 * c * s ^ 2))
          * ((Real.sqrt ((1 + 2 * (q ^ 2 * s ^ 2))⁻¹)) ^ 3
            * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)
              / (1 + 2 * (q ^ 2 * s ^ 2)))⁻¹ ^ 3) := by
        rw [hA]
        ring
    _ = c * ((1 + 2 * (q ^ 2 * s ^ 2))
          * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3)
        + (-(2 * q ^ 2 * c * s ^ 2))
          * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3 := by
        rw [hB]
    _ = c * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3 := by
        have hfinal : c * (1 + 2 * (q ^ 2 * s ^ 2)) - 2 * q ^ 2 * c * s ^ 2 = c := by ring
        calc c * ((1 + 2 * (q ^ 2 * s ^ 2))
            * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3)
            + (-(2 * q ^ 2 * c * s ^ 2))
              * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3
          = (c * (1 + 2 * (q ^ 2 * s ^ 2)) - 2 * q ^ 2 * c * s ^ 2)
              * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3 := by ring
        _ = c * Real.sqrt (((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * c ^ 2 * r ^ 2 * q ^ 2)⁻¹) ^ 3 := by
            rw [hfinal]

theorem cross_moment (r q c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2) (hr : 0 < r) (hq : 0 < q) :
    ∫ p : ℝ × ℝ, p.1 * (c * p.1 + s * p.2)
        * Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2) ∂γ2
      = c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 3 := by
  classical
  have hfun : ∀ p : ℝ × ℝ, p.1 * (c * p.1 + s * p.2)
        * Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2)
      = c * (p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
          * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2)))
        + s * (p.1 * p.2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
          * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))) := by
    intro p
    rw [bivar_exp_factor r q c s p.1 p.2]
    ring
  simp_rw [hfun]
  rcases eq_or_ne s 0 with hs0 | hs0
  · subst hs0
    simp only [zero_mul, add_zero]
    rw [integral_const_mul]
    rw [cross_T1_value r q c 0 hssq hr]
    have hmain := cross_tail r q c 0 hssq hr
    simpa [Dbloch] using hmain
  · rw [integral_add ((cross_T1_integrable r q c s hr).const_mul c)
        ((cross_T2_integrable r q c s hr hq hs0).const_mul s)]
    rw [integral_const_mul, integral_const_mul, cross_T1_value r q c s hssq hr,
      cross_T2_value r q c s hssq hr hq hs0]
    have hmain := cross_tail r q c s hssq hr
    simpa [Dbloch] using hmain

theorem cross_moment_integrable (r q c s : ℝ) (hr : 0 < r) (hq : 0 < q) :
    Integrable (fun p : ℝ × ℝ => p.1 * (c * p.1 + s * p.2)
        * Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2)) γ2 := by
  have hfun : ∀ p : ℝ × ℝ, p.1 * (c * p.1 + s * p.2)
        * Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2)
      = c * (p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
          * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2)))
        + s * (p.1 * p.2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
          * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))) := by
    intro p
    rw [bivar_exp_factor r q c s p.1 p.2]
    ring
  rcases eq_or_ne s 0 with hs0 | hs0
  · subst hs0
    have hfun0 : (fun p : ℝ × ℝ => p.1 * (c * p.1 + 0 * p.2)
        * Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + 0 * p.2) ^ 2))
      = fun p => c * (p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
        * Real.exp (-(q ^ 2 * 0 ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * 0 * p.1) * p.2))) := by
      funext p
      rw [bivar_exp_factor r q c 0 p.1 p.2]
      ring
    rw [hfun0]
    exact (cross_T1_integrable r q c 0 hr).const_mul c
  · have hfun' : (fun p : ℝ × ℝ => p.1 * (c * p.1 + s * p.2)
        * Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2))
      = fun p => c * (p.1 ^ 2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
          * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2)))
        + s * (p.1 * p.2 * (Real.exp ((-r ^ 2 - q ^ 2 * c ^ 2) * p.1 ^ 2)
          * Real.exp (-(q ^ 2 * s ^ 2) * p.2 ^ 2 - (2 * q ^ 2 * c * s * p.1) * p.2))) :=
      funext hfun
    rw [hfun']
    exact ((cross_T1_integrable r q c s hr).const_mul c).add
      ((cross_T2_integrable r q c s hr hq hs0).const_mul s)

end Rank3Gaussian
end

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology

namespace Rank3Gaussian

theorem tendsto_mul_self_atTop : Tendsto (fun t : ℝ => t * t) atTop atTop := by
  simpa [pow_two] using tendsto_pow_atTop (two_ne_zero : 2 ≠ 0)

theorem tendsto_inv_sq_atTop : Tendsto (fun t : ℝ => (t * t)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_mul_self_atTop

theorem tendsto_inv_sq_add_rpow {c p : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => ((t * t)⁻¹ + c) ^ p) atTop (𝓝 (c ^ p)) := by
  have h : Tendsto (fun t : ℝ => (t * t)⁻¹ + c) atTop (𝓝 (0 + c)) :=
    tendsto_inv_sq_atTop.add_const c
  rw [zero_add] at h
  exact h.rpow_const (Or.inl hc.ne')

theorem one_add_two_sq_rpow_eq (t : ℝ) (ht : 0 < t) (p : ℝ) :
    (1 + 2 * (t * t)) ^ p = (t * t) ^ p * ((t * t)⁻¹ + 2) ^ p := by
  rw [← Real.mul_rpow (mul_self_nonneg t) (add_nonneg (inv_nonneg.2 (mul_self_nonneg t)) (by norm_num))]
  congr 1
  rw [mul_add, mul_inv_cancel₀ (by positivity : (t*t:ℝ) ≠ 0)]
  ring

theorem sq_rpow_neg_three_halves {t : ℝ} (ht : 0 < t) :
    (t * t) ^ (-(3/2) : ℝ) = (t ^ 3)⁻¹ := by
  rw [Real.mul_rpow (le_of_lt ht) (le_of_lt ht), ← Real.rpow_add ht,
    show (-(3/2:ℝ)) + (-(3/2)) = -(3:ℝ) by norm_num,
    Real.rpow_neg (le_of_lt ht)]
  simp

theorem sq_rpow_neg_five_halves {t : ℝ} (ht : 0 < t) :
    (t * t) ^ (-(5/2) : ℝ) = (t ^ 5)⁻¹ := by
  rw [Real.mul_rpow (le_of_lt ht) (le_of_lt ht), ← Real.rpow_add ht,
    show (-(5/2:ℝ)) + (-(5/2)) = -(5:ℝ) by norm_num,
    Real.rpow_neg (le_of_lt ht)]
  simp

theorem t_cube_mul_rpow_neg_three_halves {t : ℝ} (ht : 0 < t) :
    t ^ 3 * (1 + 2 * (t * t)) ^ (-(3/2) : ℝ) = ((t * t)⁻¹ + 2) ^ (-(3/2) : ℝ) := by
  rw [one_add_two_sq_rpow_eq t ht, sq_rpow_neg_three_halves ht]
  field_simp

theorem t_pow_five_mul_rpow_neg_five_halves {t : ℝ} (ht : 0 < t) :
    t ^ 5 * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) = ((t * t)⁻¹ + 2) ^ (-(5/2) : ℝ) := by
  rw [one_add_two_sq_rpow_eq t ht, sq_rpow_neg_five_halves ht]
  field_simp

theorem rpow_neg_three_halves_two : (2:ℝ) ^ (-(3/2) : ℝ) = (2 * Real.sqrt 2)⁻¹ := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one,
    ← Real.sqrt_eq_rpow]

theorem arith_C1 : (2:ℝ) ^ (-(3/2) : ℝ) * (4/3) = Real.sqrt 2 / 3 := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [rpow_neg_three_halves_two, eq_div_iff (by norm_num : (3:ℝ) ≠ 0)]
  field_simp; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem arith_C2 : (2:ℝ) ^ (-(5/2) : ℝ) * (4/15) = Real.sqrt 2 / 30 := by
  have h25 : (2:ℝ) ^ (-(5/2) : ℝ) = (2 * Real.sqrt 2)⁻¹ * 2⁻¹ := by
    rw [show (-(5/2):ℝ) = -(3/2) + (-1) by norm_num, Real.rpow_add (by norm_num : (0:ℝ)<2),
      rpow_neg_three_halves_two, Real.rpow_neg_one]
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [h25, eq_div_iff (by norm_num : (30:ℝ) ≠ 0)]
  field_simp; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

noncomputable def F1 (t : ℝ) : ℝ :=
  (t + 4/3 * t ^ (3:ℕ)) * (1 + 2 * (t * t)) ^ (-(3/2) : ℝ)

theorem F1_deriv (t : ℝ) : HasDerivAt F1 ((1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) t := by
  have hx : (0:ℝ) < 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hsq : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t := hid.mul hid
  have hinner : HasDerivAt (fun s : ℝ => 1 + 2 * (s * s)) (2 * (t + t)) t := by
    have h : HasDerivAt ((fun s : ℝ => 1) + fun s : ℝ => 2 * (s * s)) (0 + 2 * (1 * t + t * 1)) t :=
      (hasDerivAt_const (x := t) (c := (1:ℝ))).add (hsq.const_mul 2)
    refine h.congr_deriv ?_
    ring
  have hpow : HasDerivAt (fun s : ℝ => (1 + 2 * (s * s)) ^ (-(3/2) : ℝ))
      ((2 * (t + t)) * (-(3/2)) * (1 + 2 * (t * t)) ^ ((-(3/2) : ℝ) - 1)) t :=
    hinner.rpow_const (p := -(3/2)) (Or.inl hx.ne')
  have hcube : HasDerivAt (fun s : ℝ => s ^ (3:ℕ)) (3 * t ^ (2:ℕ)) t := by
    simpa using hasDerivAt_pow 3 t
  have hnum : HasDerivAt (fun s : ℝ => s + 4/3 * s ^ (3:ℕ)) (1 + 4/3 * (3 * t ^ (2:ℕ))) t :=
    hid.add (hcube.const_mul (4/3))
  refine (hnum.mul hpow).congr_deriv ?_
  rw [show (-(3/2:ℝ) - 1) = -(5/2) by norm_num]
  have hsp : (1 + 2 * (t * t)) ^ (-(3/2) : ℝ)
      = (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) * (1 + 2 * (t * t)) := by
    have h := Real.rpow_add hx (-(5/2)) 1
    rw [show (-(5/2:ℝ)) + 1 = -(3/2) by norm_num, Real.rpow_one] at h
    exact h
  rw [hsp]
  ring

theorem F1_zero : F1 0 = 0 := by
  simp [F1]

theorem F1_tendsto : Tendsto F1 atTop (𝓝 (Real.sqrt 2 / 3)) := by
  have h3 : Tendsto (fun t : ℝ => t ^ (3:ℕ) * (1 + 2 * (t * t)) ^ (-(3/2) : ℝ))
      atTop (𝓝 ((2:ℝ) ^ (-(3/2) : ℝ))) := by
    refine (tendsto_inv_sq_add_rpow (c := 2) (p := -(3/2)) (by norm_num)).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact (t_cube_mul_rpow_neg_three_halves ht).symm
  have hc : Tendsto (fun t : ℝ => 4/3 + (t * t)⁻¹) atTop (𝓝 (4/3)) := by
    have h := tendsto_inv_sq_atTop.const_add (4/3)
    simpa [add_comm] using h
  have hmul := h3.mul hc
  rw [arith_C1] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have halg : t ^ (3:ℕ) * (4/3 + (t * t)⁻¹) = t + 4/3 * t ^ (3:ℕ) := by
    have ht2 : t * t ≠ 0 := by positivity
    field_simp; ring
  show t ^ (3:ℕ) * (1 + 2 * (t * t)) ^ (-(3/2) : ℝ) * (4/3 + (t * t)⁻¹) = F1 t
  rw [F1]
  calc t ^ (3:ℕ) * (1 + 2 * (t * t)) ^ (-(3/2) : ℝ) * (4/3 + (t * t)⁻¹)
      = (t ^ (3:ℕ) * (4/3 + (t * t)⁻¹)) * (1 + 2 * (t * t)) ^ (-(3/2) : ℝ) := by ring
    _ = (t + 4/3 * t ^ (3:ℕ)) * (1 + 2 * (t * t)) ^ (-(3/2) : ℝ) := by rw [halg]

theorem C1_aux :
    ∫ t in Set.Ioi (0:ℝ), (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) = Real.sqrt 2 / 3 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0:ℝ)) (g := F1)
    (g' := fun t : ℝ => (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) (l := Real.sqrt 2 / 3)
    (fun t _ => F1_deriv t) (fun t _ => by
      have h : (0:ℝ) ≤ 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
      positivity) F1_tendsto
  rwa [F1_zero, sub_zero] at h

theorem C1i_aux :
    IntegrableOn (fun t : ℝ => (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) (Set.Ioi (0:ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := (0:ℝ)) (g := F1)
    (g' := fun t : ℝ => (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) (l := Real.sqrt 2 / 3)
    (fun t _ => F1_deriv t) (fun t _ => by
      have h : (0:ℝ) ≤ 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
      positivity) F1_tendsto

noncomputable def G1 (t : ℝ) : ℝ :=
  (t ^ (3:ℕ) / 3 + 4 * t ^ (5:ℕ) / 15) * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)

theorem G1_deriv (t : ℝ) :
    HasDerivAt G1 (t ^ (2:ℕ) * (1 + 2 * (t * t)) ^ (-(7/2) : ℝ)) t := by
  have hx : (0:ℝ) < 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hsq : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t := hid.mul hid
  have hinner : HasDerivAt (fun s : ℝ => 1 + 2 * (s * s)) (2 * (t + t)) t := by
    have h : HasDerivAt ((fun s : ℝ => 1) + fun s : ℝ => 2 * (s * s)) (0 + 2 * (1 * t + t * 1)) t :=
      (hasDerivAt_const (x := t) (c := (1:ℝ))).add (hsq.const_mul 2)
    refine h.congr_deriv ?_
    ring
  have hpow : HasDerivAt (fun s : ℝ => (1 + 2 * (s * s)) ^ (-(5/2) : ℝ))
      ((2 * (t + t)) * (-(5/2)) * (1 + 2 * (t * t)) ^ ((-(5/2) : ℝ) - 1)) t :=
    hinner.rpow_const (p := -(5/2)) (Or.inl hx.ne')
  have h3 : HasDerivAt (fun s : ℝ => s ^ (3:ℕ) / 3) (3 * t ^ (2:ℕ) / 3) t :=
    (hasDerivAt_pow 3 t).div_const 3
  have h5 : HasDerivAt (fun s : ℝ => 4 * s ^ (5:ℕ) / 15) (4 * (5 * t ^ (5-1:ℕ)) / 15) t :=
    ((hasDerivAt_pow 5 t).const_mul 4).div_const 15
  have hnum : HasDerivAt (fun s : ℝ => s ^ (3:ℕ) / 3 + 4 * s ^ (5:ℕ) / 15)
      (3 * t ^ (2:ℕ) / 3 + 4 * (5 * t ^ (5-1:ℕ)) / 15) t := h3.add h5
  refine (hnum.mul hpow).congr_deriv ?_
  rw [show ((-(5/2) : ℝ) - 1) = -(7/2) by norm_num]
  have hsp : (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)
      = (1 + 2 * (t * t)) ^ (-(7/2) : ℝ) * (1 + 2 * (t * t)) := by
    have h := Real.rpow_add hx (-(7/2)) 1
    rw [show (-(7/2:ℝ)) + 1 = -(5/2) by norm_num, Real.rpow_one] at h
    exact h
  rw [hsp]
  ring

theorem G1_zero : G1 0 = 0 := by
  simp [G1]

theorem G1_tendsto : Tendsto G1 atTop (𝓝 (Real.sqrt 2 / 30)) := by
  have h5 : Tendsto (fun t : ℝ => t ^ (5:ℕ) * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ))
      atTop (𝓝 ((2:ℝ) ^ (-(5/2) : ℝ))) := by
    refine (tendsto_inv_sq_add_rpow (c := 2) (p := -(5/2)) (by norm_num)).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact (t_pow_five_mul_rpow_neg_five_halves ht).symm
  have hc : Tendsto (fun t : ℝ => 4/15 + (1/3) * (t * t)⁻¹) atTop (𝓝 (4/15)) := by
    have h := tendsto_inv_sq_atTop.const_mul (1/3)
    have h2 := h.const_add (4/15)
    simpa [add_comm] using h2
  have hmul := h5.mul hc
  rw [arith_C2] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have halg : t ^ (5:ℕ) * (4/15 + (1/3) * (t * t)⁻¹) = t ^ (3:ℕ) / 3 + 4 * t ^ (5:ℕ) / 15 := by
    have ht2 : t * t ≠ 0 := by positivity
    have ht5 : t ^ (5:ℕ) ≠ 0 := by positivity
    have hxx : t ^ (5:ℕ) * (t * t)⁻¹ = t ^ (3:ℕ) := by
      rw [show t ^ (5:ℕ) = t ^ (3:ℕ) * (t * t) by ring]
      field_simp
    field_simp
    ring
  show t ^ (5:ℕ) * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) * (4/15 + (1/3) * (t * t)⁻¹) = G1 t
  rw [G1]
  calc t ^ (5:ℕ) * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) * (4/15 + (1/3) * (t * t)⁻¹)
      = (t ^ (5:ℕ) * (4/15 + (1/3) * (t * t)⁻¹)) * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) := by ring
    _ = (t ^ (3:ℕ) / 3 + 4 * t ^ (5:ℕ) / 15) * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) := by rw [halg]

theorem C2_aux :
    ∫ t in Set.Ioi (0:ℝ), t ^ (2:ℕ) * (1 + 2 * (t * t)) ^ (-(7/2) : ℝ) = Real.sqrt 2 / 30 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0:ℝ)) (g := G1)
    (g' := fun t : ℝ => t ^ (2:ℕ) * (1 + 2 * (t * t)) ^ (-(7/2) : ℝ)) (l := Real.sqrt 2 / 30)
    (fun t _ => G1_deriv t) (fun t _ => by
      have h1 : (0:ℝ) ≤ t ^ (2:ℕ) := by positivity
      have h2 : (0:ℝ) ≤ 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
      positivity) G1_tendsto
  rwa [G1_zero, sub_zero] at h

theorem C2i_aux :
    IntegrableOn (fun t : ℝ => t ^ (2:ℕ) * (1 + 2 * (t * t)) ^ (-(7/2) : ℝ)) (Set.Ioi (0:ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := (0:ℝ)) (g := G1)
    (g' := fun t : ℝ => t ^ (2:ℕ) * (1 + 2 * (t * t)) ^ (-(7/2) : ℝ)) (l := Real.sqrt 2 / 30)
    (fun t _ => G1_deriv t) (fun t _ => by
      have h1 : (0:ℝ) ≤ t ^ (2:ℕ) := by positivity
      have h2 : (0:ℝ) ≤ 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
      positivity) G1_tendsto

theorem integral_Ioi_add_sq_rpow {A : ℝ} (hA : 0 < A) :
    ∫ q in Set.Ioi (0:ℝ), (A + 2 * (q * q)) ^ (-(5/2) : ℝ)
      = Real.sqrt 2 / 3 * A ^ (-2 : ℝ) := by
  have hb : (0:ℝ) < Real.sqrt A := Real.sqrt_pos.2 hA
  have hcomp : ∫ x in Set.Ioi (0:ℝ),
        (A + 2 * ((Real.sqrt A * x) * (Real.sqrt A * x))) ^ (-(5/2) : ℝ)
      = (Real.sqrt A)⁻¹ * ∫ q in Set.Ioi (0:ℝ), (A + 2 * (q * q)) ^ (-(5/2) : ℝ) := by
    have h := integral_comp_mul_left_Ioi
      (g := fun y : ℝ => (A + 2 * (y * y)) ^ (-(5/2) : ℝ)) (a := 0) hb
    simpa using h
  have hscale : ∫ x in Set.Ioi (0:ℝ),
        (A + 2 * ((Real.sqrt A * x) * (Real.sqrt A * x))) ^ (-(5/2) : ℝ)
      = A ^ (-(5/2) : ℝ) * ∫ x in Set.Ioi (0:ℝ), (1 + 2 * (x * x)) ^ (-(5/2) : ℝ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    have hfac : A + 2 * ((Real.sqrt A * x) * (Real.sqrt A * x)) = A * (1 + 2 * (x * x)) := by
      have hsqA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
      calc A + 2 * ((Real.sqrt A * x) * (Real.sqrt A * x))
          = A + 2 * (Real.sqrt A ^ 2 * (x * x)) := by ring
        _ = A + 2 * (A * (x * x)) := by rw [hsqA]
        _ = A * (1 + 2 * (x * x)) := by ring
    rw [hfac, Real.mul_rpow hA.le (by nlinarith [mul_self_nonneg x])]
  have key : (Real.sqrt A)⁻¹ * ∫ q in Set.Ioi (0:ℝ), (A + 2 * (q * q)) ^ (-(5/2) : ℝ)
      = A ^ (-(5/2) : ℝ) * (Real.sqrt 2 / 3) := by
    rw [← hcomp, hscale, C1_aux]
  have hsq : ∫ q in Set.Ioi (0:ℝ), (A + 2 * (q * q)) ^ (-(5/2) : ℝ)
      = Real.sqrt A * (A ^ (-(5/2) : ℝ) * (Real.sqrt 2 / 3)) := by
    have h := congrArg (fun z => Real.sqrt A * z) key
    rwa [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at h
  rw [hsq, Real.sqrt_eq_rpow A, ← mul_assoc, ← Real.rpow_add hA,
    show (1/2:ℝ) + (-(5/2)) = -2 by norm_num, mul_comm]

theorem tendsto_u_div_two_one_add_sq : Tendsto (fun u : ℝ => u / (2 * (1 + u * u))) atTop (𝓝 0) := by
  have h2 : Tendsto (fun u : ℝ => ((u * u)⁻¹ + 1)⁻¹) atTop (𝓝 1) := by
    have h : Tendsto (fun u : ℝ => (u * u)⁻¹ + 1) atTop (𝓝 (0 + 1)) :=
      tendsto_inv_sq_atTop.add_const 1
    rw [zero_add] at h
    simpa using h.inv₀ (by norm_num : (1:ℝ) ≠ 0)
  have h4 : Tendsto (fun u : ℝ => ((1:ℝ)/2) * u⁻¹ * ((u * u)⁻¹ + 1)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.mul h2).const_mul ((1:ℝ)/2)
    simpa [mul_assoc] using h
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have h1u : (1 + u * u) ≠ 0 := by nlinarith [mul_self_nonneg u]
  field_simp

noncomputable def K (u : ℝ) : ℝ := u / (2 * (1 + u * u)) + Real.arctan u / 2

theorem K_deriv (u : ℝ) : HasDerivAt K (((1 + u * u) ^ 2)⁻¹) u := by
  have hx : (0:ℝ) < 1 + u * u := by nlinarith [mul_self_nonneg u]
  have hid : HasDerivAt (fun s : ℝ => s) 1 u := hasDerivAt_id u
  have hsqd : HasDerivAt (fun s : ℝ => s * s) (1 * u + u * 1) u := hid.mul hid
  have hbase : HasDerivAt (fun s : ℝ => 1 + s * s) (u + u) u := by
    have h : HasDerivAt ((fun s : ℝ => 1) + fun s : ℝ => s * s) (0 + (1 * u + u * 1)) u :=
      (hasDerivAt_const (x := u) (c := (1:ℝ))).add hsqd
    rw [show ((fun s : ℝ => 1) + fun s : ℝ => s * s) = (fun s : ℝ => 1 + s * s) from by
      funext s; simp [Pi.add_apply]] at h
    exact h.congr_deriv (by ring)
  have hden : HasDerivAt (fun s : ℝ => 2 * (1 + s * s)) (2 * (u + u)) u := hbase.const_mul 2
  have hK1 : HasDerivAt (fun s : ℝ => s / (2 * (1 + s * s)))
      ((1 * (2 * (1 + u * u)) - u * (2 * (u + u))) / (2 * (1 + u * u)) ^ 2) u :=
    hid.div hden (by positivity)
  have harct : HasDerivAt (fun s : ℝ => Real.arctan s / 2) ((1 / (1 + u * u)) / 2) u := by
    have h := (Real.hasDerivAt_arctan u).div_const 2
    simpa [pow_two] using h
  have hsum : HasDerivAt (fun s : ℝ => s / (2 * (1 + s * s)) + Real.arctan s / 2)
      ((1 * (2 * (1 + u * u)) - u * (2 * (u + u))) / (2 * (1 + u * u)) ^ 2 + (1 / (1 + u * u)) / 2) u := by
    have h := hK1.add harct
    rw [show ((fun s : ℝ => s / (2 * (1 + s * s))) + fun s : ℝ => Real.arctan s / 2)
        = (fun s : ℝ => s / (2 * (1 + s * s)) + Real.arctan s / 2) from by
      funext s; simp [Pi.add_apply]] at h
    exact h
  rw [show K = (fun s : ℝ => s / (2 * (1 + s * s)) + Real.arctan s / 2) from rfl]
  refine hsum.congr_deriv ?_
  have h1u : (1 + u * u) ≠ 0 := ne_of_gt hx
  have h2u : (2 * (1 + u * u)) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem K_zero : K 0 = 0 := by
  simp [K]

theorem K_tendsto : Tendsto K atTop (𝓝 (Real.pi / 4)) := by
  have h1 : Tendsto (fun u : ℝ => u / (2 * (1 + u * u))) atTop (𝓝 0) :=
    tendsto_u_div_two_one_add_sq
  have h2 : Tendsto (fun u : ℝ => Real.arctan u / 2) atTop (𝓝 (Real.pi / 4)) := by
    have h := (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).div_const 2
    have hpi : Real.pi / 2 / 2 = Real.pi / 4 := by ring
    rw [hpi] at h
    exact h
  have hsum : Tendsto (fun u : ℝ => u / (2 * (1 + u * u)) + Real.arctan u / 2) atTop (𝓝 (0 + Real.pi / 4)) :=
    h1.add h2
  rw [show K = (fun u : ℝ => u / (2 * (1 + u * u)) + Real.arctan u / 2) from rfl]
  simpa using hsum

theorem integral_Ioi_one_add_sq_inv_sq :
    ∫ u in Set.Ioi (0:ℝ), ((1 + u * u) ^ 2)⁻¹ = Real.pi / 4 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0:ℝ)) (g := K)
    (g' := fun u : ℝ => ((1 + u * u) ^ 2)⁻¹) (l := Real.pi / 4)
    (fun u _ => K_deriv u) (fun u _ => by
      have h1 : (0:ℝ) ≤ 1 + u * u := by nlinarith [mul_self_nonneg u]
      positivity) K_tendsto
  rwa [K_zero, sub_zero] at h

theorem integral_Ioi_one_add_two_sq_inv_sq :
    ∫ r in Set.Ioi (0:ℝ), ((1 + 2 * (r * r)) ^ 2)⁻¹ = Real.pi / (4 * Real.sqrt 2) := by
  have hb : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hcomp : ∫ r in Set.Ioi (0:ℝ), ((1 + (Real.sqrt 2 * r) * (Real.sqrt 2 * r)) ^ 2)⁻¹
      = (Real.sqrt 2)⁻¹ * ∫ u in Set.Ioi (0:ℝ), ((1 + u * u) ^ 2)⁻¹ := by
    have h := integral_comp_mul_left_Ioi (g := fun u : ℝ => ((1 + u * u) ^ 2)⁻¹) (a := 0) hb
    simpa using h
  have hscale : ∫ r in Set.Ioi (0:ℝ), ((1 + (Real.sqrt 2 * r) * (Real.sqrt 2 * r)) ^ 2)⁻¹
      = ∫ r in Set.Ioi (0:ℝ), ((1 + 2 * (r * r)) ^ 2)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpt : 1 + (Real.sqrt 2 * r) * (Real.sqrt 2 * r) = 1 + 2 * (r * r) := by
      calc 1 + (Real.sqrt 2 * r) * (Real.sqrt 2 * r)
          = 1 + Real.sqrt 2 ^ 2 * (r * r) := by ring
        _ = 1 + 2 * (r * r) := by rw [hsq2]
    rw [hpt]
  rw [hscale, integral_Ioi_one_add_sq_inv_sq] at hcomp
  rw [hcomp, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

theorem rpow_neg_two_eq_inv_sq {x : ℝ} (hx : 0 ≤ x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx]
  exact congrArg Inv.inv (Real.rpow_natCast x 2)

theorem C3_aux :
    ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ), (1 + 2 * (r * r) + 2 * (q * q)) ^ (-(5/2) : ℝ)
      = Real.pi / 12 := by
  have hinner : ∀ r : ℝ, ∫ q in Set.Ioi (0:ℝ), (1 + 2 * (r * r) + 2 * (q * q)) ^ (-(5/2) : ℝ)
      = Real.sqrt 2 / 3 * (1 + 2 * (r * r)) ^ (-2 : ℝ) := by
    intro r
    have hA : (0:ℝ) < 1 + 2 * (r * r) := by nlinarith [mul_self_nonneg r]
    exact integral_Ioi_add_sq_rpow hA
  have hconv : ∀ r : ℝ, (1 + 2 * (r * r)) ^ (-2 : ℝ) = ((1 + 2 * (r * r)) ^ 2)⁻¹ := by
    intro r; exact rpow_neg_two_eq_inv_sq (by nlinarith [mul_self_nonneg r])
  calc ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ), (1 + 2 * (r * r) + 2 * (q * q)) ^ (-(5/2) : ℝ)
      = ∫ r in Set.Ioi (0:ℝ), Real.sqrt 2 / 3 * (1 + 2 * (r * r)) ^ (-2 : ℝ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => hinner r)
    _ = Real.sqrt 2 / 3 * ∫ r in Set.Ioi (0:ℝ), (1 + 2 * (r * r)) ^ (-2 : ℝ) := by
        rw [integral_const_mul]
    _ = Real.sqrt 2 / 3 * (Real.pi / (4 * Real.sqrt 2)) := by
        rw [show (∫ r in Set.Ioi (0:ℝ), (1 + 2 * (r * r)) ^ (-2 : ℝ))
            = ∫ r in Set.Ioi (0:ℝ), ((1 + 2 * (r * r)) ^ 2)⁻¹ from by
          refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => hconv r),
          integral_Ioi_one_add_two_sq_inv_sq]
    _ = Real.pi / 12 := by
        have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
        field_simp
        ring

theorem integrable_inv_one_add_mul_self : Integrable (fun s : ℝ => (1 + s * s)⁻¹) := by
  simpa [pow_two] using integrable_inv_one_add_sq

theorem C3i_aux :
    IntegrableOn (fun p : ℝ × ℝ => (1 + 2 * (p.1 * p.1) + 2 * (p.2 * p.2)) ^ (-(5/2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  have hh : Integrable (fun s : ℝ => (1 + s * s)⁻¹) := integrable_inv_one_add_mul_self
  have hprod : Integrable (fun p : ℝ × ℝ => (1 + p.1 * p.1)⁻¹ * (1 + p.2 * p.2)⁻¹)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    hh.integrableOn.mul_prod hh.integrableOn
  have hcont : Continuous (fun p : ℝ × ℝ => (1 + 2 * (p.1 * p.1) + 2 * (p.2 * p.2)) ^ (-(5/2) : ℝ)) := by
    have hbase : Continuous (fun p : ℝ × ℝ => 1 + 2 * (p.1 * p.1) + 2 * (p.2 * p.2)) := by fun_prop
    refine hbase.rpow_const (fun p => Or.inl ?_)
    have h1 : (0:ℝ) ≤ p.1 * p.1 := mul_self_nonneg p.1
    have h2 : (0:ℝ) ≤ p.2 * p.2 := mul_self_nonneg p.2
    positivity
  have hmono : Integrable (fun p : ℝ × ℝ => (1 + 2 * (p.1 * p.1) + 2 * (p.2 * p.2)) ^ (-(5/2) : ℝ))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    refine hprod.mono' (hcont.measurable.aestronglyMeasurable) ?_
    filter_upwards with p
    obtain ⟨r, q⟩ := p
    have hr : (0:ℝ) ≤ r * r := mul_self_nonneg r
    have hq : (0:ℝ) ≤ q * q := mul_self_nonneg q
    have hX : (0:ℝ) < 1 + 2 * (r * r) + 2 * (q * q) := by linarith
    have hX1 : (1:ℝ) ≤ 1 + 2 * (r * r) + 2 * (q * q) := by linarith
    have hY : (0:ℝ) < (1 + r * r) * (1 + q * q) := by
      have h1 : (0:ℝ) < 1 + r * r := by linarith
      have h2 : (0:ℝ) < 1 + q * q := by linarith
      positivity
    have hYX : (1 + r * r) * (1 + q * q) ≤ (1 + 2 * (r * r) + 2 * (q * q)) ^ 2 := by
      nlinarith [hr, hq, sq_nonneg (r * r), sq_nonneg (q * q)]
    have hpow : (1 + 2 * (r * r) + 2 * (q * q)) ^ (2:ℕ)
        ≤ (1 + 2 * (r * r) + 2 * (q * q)) ^ ((5:ℝ)/2) := by
      rw [← Real.rpow_natCast (1 + 2 * (r * r) + 2 * (q * q)) 2]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hX.le _)]
    rw [show (1 + 2 * (r * r) + 2 * (q * q)) ^ (-(5/2) : ℝ)
        = ((1 + 2 * (r * r) + 2 * (q * q)) ^ ((5:ℝ)/2))⁻¹ from by rw [Real.rpow_neg hX.le]]
    rw [show (1 + r * r)⁻¹ * (1 + q * q)⁻¹ = ((1 + r * r) * (1 + q * q))⁻¹ from by rw [mul_inv]]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hX _) hY).mpr (le_trans hYX hpow)
  rwa [Measure.prod_restrict] at hmono

theorem C1 :
    ∫ t in Set.Ioi (0:ℝ), (1 + 2 * t ^ 2) ^ (-(5/2) : ℝ) = Real.sqrt 2 / 3 := by
  rw [show (∫ t in Set.Ioi (0:ℝ), (1 + 2 * t ^ 2) ^ (-(5/2) : ℝ))
      = ∫ t in Set.Ioi (0:ℝ), (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) from by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [pow_two]]
  exact C1_aux

theorem C1i :
    IntegrableOn (fun t : ℝ => (1 + 2 * t ^ 2) ^ (-(5/2) : ℝ)) (Set.Ioi 0) := by
  rw [show (fun t : ℝ => (1 + 2 * t ^ 2) ^ (-(5/2) : ℝ))
      = (fun t : ℝ => (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) from by
    funext t
    simp only [pow_two]]
  exact C1i_aux

theorem C2 :
    ∫ t in Set.Ioi (0:ℝ), t ^ 2 * (1 + 2 * t ^ 2) ^ (-(7/2) : ℝ) = Real.sqrt 2 / 30 := by
  rw [show (∫ t in Set.Ioi (0:ℝ), t ^ 2 * (1 + 2 * t ^ 2) ^ (-(7/2) : ℝ))
      = ∫ t in Set.Ioi (0:ℝ), t ^ (2:ℕ) * (1 + 2 * (t * t)) ^ (-(7/2) : ℝ) from by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [pow_two]]
  exact C2_aux

theorem C2i :
    IntegrableOn (fun t : ℝ => t ^ 2 * (1 + 2 * t ^ 2) ^ (-(7/2) : ℝ)) (Set.Ioi 0) := by
  rw [show (fun t : ℝ => t ^ 2 * (1 + 2 * t ^ 2) ^ (-(7/2) : ℝ))
      = (fun t : ℝ => t ^ (2:ℕ) * (1 + 2 * (t * t)) ^ (-(7/2) : ℝ)) from by
    funext t
    simp only [pow_two]]
  exact C2i_aux

theorem C3 :
    ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ), (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5/2) : ℝ)
      = Real.pi / 12 := by
  rw [show (∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ), (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5/2) : ℝ))
      = ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ),
          (1 + 2 * (r * r) + 2 * (q * q)) ^ (-(5/2) : ℝ) from by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun q _ => ?_)
    simp only [pow_two]]
  exact C3_aux

theorem C3i :
    IntegrableOn (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5/2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  rw [show (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5/2) : ℝ))
      = (fun rq : ℝ × ℝ => (1 + 2 * (rq.1 * rq.1) + 2 * (rq.2 * rq.2)) ^ (-(5/2) : ℝ)) from by
    funext rq
    simp only [pow_two]]
  exact C3i_aux

theorem sq_rpow_neg_one_half {t : ℝ} (ht : 0 < t) : (t * t) ^ (-(1/2) : ℝ) = t⁻¹ := by
  rw [Real.mul_rpow (le_of_lt ht) (le_of_lt ht), ← Real.rpow_add ht,
    show (-(1/2:ℝ)) + (-(1/2)) = -1 by norm_num, Real.rpow_neg_one]

theorem t_mul_rpow_neg_one_half {t : ℝ} (ht : 0 < t) :
    t * (1 + 2 * (t * t)) ^ (-(1/2) : ℝ) = ((t * t)⁻¹ + 2) ^ (-(1/2) : ℝ) := by
  rw [one_add_two_sq_rpow_eq t ht, sq_rpow_neg_one_half ht]
  field_simp

noncomputable def F0 (t : ℝ) : ℝ := t * (1 + 2 * (t * t)) ^ (-(1/2) : ℝ)

theorem F0_deriv (t : ℝ) : HasDerivAt F0 ((1 + 2 * (t * t)) ^ (-(3/2) : ℝ)) t := by
  have hx : (0:ℝ) < 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hsq : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t := hid.mul hid
  have hinner : HasDerivAt (fun s : ℝ => 1 + 2 * (s * s)) (2 * (t + t)) t := by
    have h : HasDerivAt ((fun s : ℝ => 1) + fun s : ℝ => 2 * (s * s)) (0 + 2 * (1 * t + t * 1)) t :=
      (hasDerivAt_const (x := t) (c := (1:ℝ))).add (hsq.const_mul 2)
    rw [show ((fun s : ℝ => 1) + fun s : ℝ => 2 * (s * s)) = (fun s : ℝ => 1 + 2 * (s * s)) from by
      funext s; simp [Pi.add_apply]] at h
    exact h.congr_deriv (by ring)
  have hpow : HasDerivAt (fun s : ℝ => (1 + 2 * (s * s)) ^ (-(1/2) : ℝ))
      ((2 * (t + t)) * (-(1/2)) * (1 + 2 * (t * t)) ^ ((-(1/2) : ℝ) - 1)) t :=
    hinner.rpow_const (p := -(1/2)) (Or.inl hx.ne')
  refine (hid.mul hpow).congr_deriv ?_
  rw [show ((-(1/2) : ℝ) - 1) = -(3/2) by norm_num]
  have hsp : (1 + 2 * (t * t)) ^ (-(1/2) : ℝ)
      = (1 + 2 * (t * t)) ^ (-(3/2) : ℝ) * (1 + 2 * (t * t)) := by
    have h := Real.rpow_add hx (-(3/2)) 1
    rw [show (-(3/2:ℝ)) + 1 = -(1/2) by norm_num, Real.rpow_one] at h
    exact h
  rw [hsp]; ring

theorem F0_zero : F0 0 = 0 := by simp [F0]

theorem arith_half : (2:ℝ) ^ (-(1/2) : ℝ) = 1 / Real.sqrt 2 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
  rw [one_div]

theorem F0_tendsto : Tendsto F0 atTop (𝓝 (1 / Real.sqrt 2)) := by
  have h3 : Tendsto (fun t : ℝ => ((t * t)⁻¹ + 2) ^ (-(1/2) : ℝ)) atTop (𝓝 ((2:ℝ) ^ (-(1/2) : ℝ))) :=
    tendsto_inv_sq_add_rpow (c := 2) (p := -(1/2)) (by norm_num)
  rw [arith_half] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact (t_mul_rpow_neg_one_half ht).symm

theorem integral_Ioi_one_add_two_sq_rpow_neg_three_halves :
    ∫ t in Set.Ioi (0:ℝ), (1 + 2 * (t * t)) ^ (-(3/2) : ℝ) = 1 / Real.sqrt 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0:ℝ)) (g := F0)
    (g' := fun t : ℝ => (1 + 2 * (t * t)) ^ (-(3/2) : ℝ)) (l := 1 / Real.sqrt 2)
    (fun t _ => F0_deriv t) (fun t _ => by
      have h1 : (0:ℝ) ≤ 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
      positivity) F0_tendsto
  rwa [F0_zero, sub_zero] at h

theorem integrableOn_one_add_two_sq_rpow_neg_three_halves :
    IntegrableOn (fun t : ℝ => (1 + 2 * (t * t)) ^ (-(3/2) : ℝ)) (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := (0:ℝ)) (g := F0)
    (g' := fun t : ℝ => (1 + 2 * (t * t)) ^ (-(3/2) : ℝ)) (l := 1 / Real.sqrt 2)
    (fun t _ => F0_deriv t) (fun t _ => by
      have h1 : (0:ℝ) ≤ 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
      positivity) F0_tendsto

theorem integral_Ioi_sq_mul_one_add_two_sq_rpow :
    ∫ t in Set.Ioi (0:ℝ), t * t * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) = Real.sqrt 2 / 12 := by
  have hpt : ∀ t : ℝ, t * t * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)
      = (1/2) * ((1 + 2 * (t * t)) ^ (-(3/2) : ℝ) - (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) := by
    intro t
    have hx : (0:ℝ) < 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
    have h1 : (1 + 2 * (t * t)) ^ (-(3/2) : ℝ)
        = (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) * (1 + 2 * (t * t)) := by
      have h := Real.rpow_add hx (-(5/2)) 1
      rw [show (-(5/2:ℝ)) + 1 = -(3/2) by norm_num, Real.rpow_one] at h
      exact h
    rw [h1]; ring
  have hAB : ∫ t in Set.Ioi (0:ℝ),
      ((1 + 2 * (t * t)) ^ (-(3/2) : ℝ) - (1 + 2 * (t * t)) ^ (-(5/2) : ℝ))
      = 1 / Real.sqrt 2 - Real.sqrt 2 / 3 := by
    rw [integral_sub (integrableOn_one_add_two_sq_rpow_neg_three_halves) C1i_aux,
      integral_Ioi_one_add_two_sq_rpow_neg_three_halves, C1_aux]
  calc ∫ t in Set.Ioi (0:ℝ), t * t * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)
      = ∫ t in Set.Ioi (0:ℝ),
          (1/2) * ((1 + 2 * (t * t)) ^ (-(3/2) : ℝ) - (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t)
    _ = (1/2) * (1 / Real.sqrt 2 - Real.sqrt 2 / 3) := by
        rw [integral_const_mul, hAB]
    _ = Real.sqrt 2 / 12 := by
        have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
        field_simp
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem integrableOn_sq_mul_one_add_two_sq_rpow :
    IntegrableOn (fun t : ℝ => t * t * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) (Set.Ioi 0) := by
  have hmaj : IntegrableOn (fun t : ℝ => (1/2 : ℝ) * (1 + 2 * (t * t)) ^ (-(3/2) : ℝ))
      (Set.Ioi 0) :=
    integrableOn_one_add_two_sq_rpow_neg_three_halves.const_mul (1/2 : ℝ)
  have hcont : Continuous (fun t : ℝ => t * t * (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) := by
    have hb : Continuous (fun t : ℝ => 1 + 2 * (t * t)) := by fun_prop
    have hp : Continuous (fun t : ℝ => (1 + 2 * (t * t)) ^ (-(5/2) : ℝ)) :=
      hb.rpow_const (fun t => Or.inl (by nlinarith [mul_self_nonneg t]))
    exact (by fun_prop : Continuous fun t : ℝ => t * t).mul hp
  refine hmaj.mono' hcont.measurable.aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have hx : (0:ℝ) < 1 + 2 * (t * t) := by nlinarith [mul_self_nonneg t]
  have h1 : (1 + 2 * (t * t)) ^ (-(3/2) : ℝ)
      = (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) * (1 + 2 * (t * t)) := by
    have h := Real.rpow_add hx (-(5/2)) 1
    rw [show (-(5/2:ℝ)) + 1 = -(3/2) by norm_num, Real.rpow_one] at h
    exact h
  have hnn : (0:ℝ) ≤ (1 + 2 * (t * t)) ^ (-(5/2) : ℝ) := Real.rpow_nonneg hx.le _
  rw [Real.norm_of_nonneg (mul_nonneg (mul_self_nonneg t) hnn)]
  rw [h1]
  nlinarith [hnn]

end Rank3Gaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace BrickD

open Rank3Gaussian

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

lemma sq_le_one {c : ℝ} (hc : c ∈ Set.Icc (-1) 1) : c ^ 2 ≤ 1 := by
  obtain ⟨h1, h2⟩ := hc
  nlinarith

lemma base_pos (r q : ℝ) : 0 < 1 + 2 * r ^ 2 + 2 * q ^ 2 := by positivity

lemma sep_pos (r q : ℝ) : 0 < (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) := by positivity

lemma base_le_sep (r q : ℝ) :
    1 + 2 * r ^ 2 + 2 * q ^ 2 ≤ (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) := by
  nlinarith [sq_nonneg r, sq_nonneg q, mul_nonneg (sq_nonneg r) (sq_nonneg q)]

lemma base_le_Dbloch (r q c : ℝ) (hc : c ^ 2 ≤ 1) :
    1 + 2 * r ^ 2 + 2 * q ^ 2 ≤ Dbloch r q c := by
  have h1 : (0:ℝ) ≤ r ^ 2 * q ^ 2 := by positivity
  have h2 : (0:ℝ) ≤ 1 - c ^ 2 := by linarith
  have h3 : (0:ℝ) ≤ 4 * r ^ 2 * q ^ 2 * (1 - c ^ 2) := by nlinarith [mul_nonneg h1 h2]
  unfold Dbloch
  nlinarith [h3]

lemma Dbloch_pos (r q c : ℝ) (hc : c ^ 2 ≤ 1) : 0 < Dbloch r q c :=
  lt_of_lt_of_le (base_pos r q) (base_le_Dbloch r q c hc)

lemma one_add_tangent_le_rpow (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    1 + (5/2) * z ≤ (1 - z) ^ (-(5/2) : ℝ) := by
  have hpos : (0:ℝ) < 1 - z := by linarith
  have hbase : (0:ℝ) ≤ 1 + (5/2) * z := by positivity
  have h1 : (1 + (5/2) * z) ^ ((2:ℝ)/5) ≤ 1 + z := by
    have h := rpow_one_add_le_one_add_mul_self (s := (5/2) * z) (p := (2:ℝ)/5)
      (by linarith) (by norm_num) (by norm_num)
    calc (1 + (5/2) * z) ^ ((2:ℝ)/5) ≤ 1 + (2/5) * ((5/2) * z) := h
      _ = 1 + z := by ring
  have h2 : 1 + z ≤ (1 - z)⁻¹ := by
    rw [← one_div, le_div_iff₀ hpos]
    nlinarith [sq_nonneg z]
  have h3 : 1 + (5/2) * z ≤ ((1 - z)⁻¹) ^ ((5:ℝ)/2) := by
    calc 1 + (5/2) * z = ((1 + (5/2) * z) ^ ((2:ℝ)/5)) ^ ((5:ℝ)/2) := by
          rw [← Real.rpow_mul hbase]; norm_num
      _ ≤ (1 + z) ^ ((5:ℝ)/2) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      _ ≤ ((1 - z)⁻¹) ^ ((5:ℝ)/2) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  refine le_trans h3 (le_of_eq ?_)
  rw [Real.inv_rpow (le_of_lt hpos), ← Real.rpow_neg (le_of_lt hpos)]

lemma Dbloch_rpow_le (r q c : ℝ) (hc : c ^ 2 ≤ 1) :
    (Dbloch r q c) ^ (-(5/2) : ℝ) ≤ (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5/2) : ℝ) :=
  Real.rpow_le_rpow_of_nonpos (base_pos r q) (base_le_Dbloch r q c hc) (by norm_num)

lemma sep_rpow_le (r q : ℝ) :
    ((1 + 2 * r ^ 2) * (1 + 2 * q ^ 2)) ^ (-(5/2) : ℝ)
      ≤ (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5/2) : ℝ) :=
  Real.rpow_le_rpow_of_nonpos (base_pos r q) (base_le_sep r q) (by norm_num)

lemma Dbloch_rpow_ge (r q c : ℝ) (hc : c ^ 2 ≤ 1) :
    ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(5/2) : ℝ)
        + 10 * c^2 * r^2 * q^2 * ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(7/2) : ℝ)
      ≤ (Dbloch r q c) ^ (-(5/2) : ℝ) := by
  have hsep : (0:ℝ) < (1 + 2*r^2) * (1 + 2*q^2) := sep_pos r q
  have hprod : (0:ℝ) ≤ 4 * r ^ 2 * q ^ 2 * (1 - c ^ 2) := by
    have h1 : (0:ℝ) ≤ r ^ 2 * q ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ 1 - c ^ 2 := by linarith
    nlinarith [mul_nonneg h1 h2]
  have h4 : 4 * c ^ 2 * r ^ 2 * q ^ 2 ≤ 4 * r ^ 2 * q ^ 2 := by nlinarith [hprod]
  have h5 : 4 * r ^ 2 * q ^ 2 < (1 + 2*r^2) * (1 + 2*q^2) := by
    nlinarith [sq_nonneg r, sq_nonneg q]
  have hZ1 : 4 * c^2 * r^2 * q^2 / ((1 + 2*r^2) * (1 + 2*q^2)) < 1 := by
    rw [div_lt_one hsep]; linarith
  have hZn : (0:ℝ) ≤ 4 * c^2 * r^2 * q^2 / ((1 + 2*r^2) * (1 + 2*q^2)) := by positivity
  have htan := one_add_tangent_le_rpow _ hZn hZ1
  have hfactor : Dbloch r q c
      = ((1 + 2*r^2) * (1 + 2*q^2)) * (1 - 4 * c^2 * r^2 * q^2 / ((1 + 2*r^2) * (1 + 2*q^2))) := by
    unfold Dbloch
    field_simp
  have hkey : ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(5/2) : ℝ) / ((1 + 2*r^2) * (1 + 2*q^2))
      = ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(7/2) : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hsep]
    norm_num
  have hsp : (0:ℝ) ≤ ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(5/2) : ℝ) := by positivity
  rw [hfactor, Real.mul_rpow (le_of_lt hsep) (by positivity :
    (0:ℝ) ≤ 1 - 4 * c^2 * r^2 * q^2 / ((1 + 2*r^2) * (1 + 2*q^2)))]
  calc ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(5/2) : ℝ)
          + 10 * c^2 * r^2 * q^2 * ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(7/2) : ℝ)
      = ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(5/2) : ℝ)
          * (1 + (5/2) * (4 * c^2 * r^2 * q^2 / ((1 + 2*r^2) * (1 + 2*q^2)))) := by
        rw [← hkey]; field_simp; ring
    _ ≤ ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(5/2) : ℝ)
          * (1 - 4 * c^2 * r^2 * q^2 / ((1 + 2*r^2) * (1 + 2*q^2))) ^ (-(5/2) : ℝ) :=
        mul_le_mul_of_nonneg_left htan hsp

lemma Dbloch_rpow_ge' (r q u : ℝ) (hu : u ^ 2 ≤ 1) :
    (1 + 2*r^2) ^ (-(5/2) : ℝ) * (1 + 2*q^2) ^ (-(5/2) : ℝ)
        + 10 * u^2 * ((r^2 * (1 + 2*r^2) ^ (-(7/2) : ℝ))
            * (q^2 * (1 + 2*q^2) ^ (-(7/2) : ℝ)))
      ≤ (Dbloch r q (-u)) ^ (-(5/2) : ℝ) := by
  have hc : (-u) ^ 2 ≤ 1 := by nlinarith
  have hmain := Dbloch_rpow_ge r q (-u) hc
  have hEq : ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(5/2) : ℝ)
        + 10 * (-u)^2 * r^2 * q^2 * ((1 + 2*r^2) * (1 + 2*q^2)) ^ (-(7/2) : ℝ)
      = (1 + 2*r^2) ^ (-(5/2) : ℝ) * (1 + 2*q^2) ^ (-(5/2) : ℝ)
        + 10 * u^2 * ((r^2 * (1 + 2*r^2) ^ (-(7/2) : ℝ))
            * (q^2 * (1 + 2*q^2) ^ (-(7/2) : ℝ))) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    ring
  rwa [hEq] at hmain

lemma integral_iter_eq (F : ℝ → ℝ → ℝ)
    (hF : Integrable (fun z : ℝ × ℝ => F z.1 z.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))) :
    (∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ), F r q)
      = ∫ z : ℝ × ℝ, F z.1 z.2
          ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  rw [integral_prod (f := fun z : ℝ × ℝ => F z.1 z.2) hF]

lemma integrable_dom
    (hC3i : IntegrableOn
      (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5/2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0)) :
    Integrable (fun z : ℝ × ℝ => (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  rw [Measure.prod_restrict]
  exact hC3i

lemma integrable_blast (c : ℝ) (hc : c ^ 2 ≤ 1)
    (hdom : Integrable (fun z : ℝ × ℝ => (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))) :
    Integrable (fun z : ℝ × ℝ => (Dbloch z.1 z.2 c) ^ (-(5/2) : ℝ))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  have hcont : Continuous fun z : ℝ × ℝ => Dbloch z.1 z.2 c := by
    unfold Dbloch
    continuity
  have hcont2 : Continuous fun z : ℝ × ℝ => (Dbloch z.1 z.2 c) ^ (-(5/2) : ℝ) :=
    hcont.rpow_const (fun z => Or.inl (ne_of_gt (Dbloch_pos z.1 z.2 c hc)))
  refine Integrable.mono' hdom hcont2.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro z
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (le_of_lt (Dbloch_pos z.1 z.2 c hc)) _)]
  exact Dbloch_rpow_le z.1 z.2 c hc

theorem bovInt_le_self {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hC3 : ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ), (1 + 2*r^2 + 2*q^2)^(-(5/2):ℝ)
      = Real.pi/12)
    (hC3i : IntegrableOn
      (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5/2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0)) :
    bovInt c ≤ c := by
  have hc : c ^ 2 ≤ 1 := by nlinarith
  have hGint := integrable_dom hC3i
  have hFint := integrable_blast c hc hGint
  have hmono :
      ∫ z : ℝ × ℝ, (Dbloch z.1 z.2 c) ^ (-(5/2) : ℝ)
        ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))
      ≤ ∫ z : ℝ × ℝ, (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ)
        ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    integral_mono hFint hGint (fun z => Dbloch_rpow_le z.1 z.2 c hc)
  calc bovInt c
      = (12*c/Real.pi) * ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ),
          (Dbloch r q c) ^ (-(5/2) : ℝ) := rfl
    _ = (12*c/Real.pi) * ∫ z : ℝ × ℝ, (Dbloch z.1 z.2 c) ^ (-(5/2) : ℝ)
          ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
        rw [integral_iter_eq (fun r q => (Dbloch r q c) ^ (-(5/2) : ℝ)) hFint]
    _ ≤ (12*c/Real.pi) * ∫ z : ℝ × ℝ, (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ)
          ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
        apply mul_le_mul_of_nonneg_left hmono
        positivity
    _ = (12*c/Real.pi) * (∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ),
          (1 + 2*r^2 + 2*q^2)^(-(5/2):ℝ)) := by
        rw [integral_iter_eq (fun r q => (1 + 2*r^2 + 2*q^2)^(-(5/2):ℝ)) hGint]
    _ = (12*c/Real.pi) * (Real.pi/12) := by rw [hC3]
    _ = c := by
        field_simp

lemma arith_cubic (u : ℝ) (hu : 0 ≤ u) :
    (0:ℝ) ≤ 500000 * u ^ 3 - 619537 * u + 270963 := by
  have h1 : (0:ℝ) ≤ 500000 * (u - 9/14) ^ 2 * (u + 9/7) := by
    have h2 : (0:ℝ) ≤ u + 9/7 := by linarith
    positivity
  have h3 : (0:ℝ) ≤ 17687/49 * u + 1815309/343 := by positivity
  nlinarith [h1, h3]

lemma arith_main (u : ℝ) (hu : 0 ≤ u) :
    0.954 * u - 0.046 ≤ (12/Real.pi) * (2*u/9 + u^3/45) := by
  have hpi : (5000:ℝ)/1309 ≤ 12/Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hcub := arith_cubic u hu
  have hstep : 0.954 * u - 0.046 ≤ (5000/1309) * (2*u/9 + u^3/45) := by
    nlinarith [hcub]
  have hpos2 : (0:ℝ) ≤ 2*u/9 + u^3/45 := by positivity
  exact le_trans hstep (mul_le_mul_of_nonneg_right hpi hpos2)

noncomputable def loA (z : ℝ × ℝ) : ℝ := (1 + 2*z.1^2)^(-(5/2):ℝ) * (1 + 2*z.2^2)^(-(5/2):ℝ)

noncomputable def loB (z : ℝ × ℝ) : ℝ :=
  (z.1^2 * (1 + 2*z.1^2)^(-(7/2):ℝ)) * (z.2^2 * (1 + 2*z.2^2)^(-(7/2):ℝ))

noncomputable def lo (u : ℝ) (z : ℝ × ℝ) : ℝ := loA z + 10*u^2 * loB z

lemma loA_nonneg (z : ℝ × ℝ) : 0 ≤ loA z := by
  simp only [loA]
  positivity

lemma loB_nonneg (z : ℝ × ℝ) : 0 ≤ loB z := by
  simp only [loB]
  positivity

lemma cont_loA : Continuous fun z : ℝ × ℝ => loA z := by
  simp only [loA]
  exact Continuous.mul
    (Continuous.rpow_const (by continuity) (fun z => Or.inl (by positivity)))
    (Continuous.rpow_const (by continuity) (fun z => Or.inl (by positivity)))

lemma cont_loB : Continuous fun z : ℝ × ℝ => loB z := by
  simp only [loB]
  exact Continuous.mul
    (Continuous.mul (by continuity)
      (Continuous.rpow_const (by continuity) (fun z => Or.inl (by positivity))))
    (Continuous.mul (by continuity)
      (Continuous.rpow_const (by continuity) (fun z => Or.inl (by positivity))))

lemma loA_le (z : ℝ × ℝ) :
    loA z ≤ (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ) := by
  rw [loA, ← Real.mul_rpow (by positivity : (0:ℝ) ≤ 1 + 2*z.1^2)
    (by positivity : (0:ℝ) ≤ 1 + 2*z.2^2)]
  exact sep_rpow_le z.1 z.2

lemma lo_le (u : ℝ) (hu : u ^ 2 ≤ 1) (z : ℝ × ℝ) :
    lo u z ≤ (Dbloch z.1 z.2 (-u)) ^ (-(5/2) : ℝ) :=
  Dbloch_rpow_ge' z.1 z.2 u hu

lemma lo_chain (u : ℝ) (hu : u ^ 2 ≤ 1) (z : ℝ × ℝ) :
    10*u^2 * loB z ≤ (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ) :=
  le_trans (le_trans (le_add_of_nonneg_left (loA_nonneg z)) (lo_le u hu z))
    (Dbloch_rpow_le z.1 z.2 (-u) (by nlinarith))

theorem bovInt_neg_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hC1 : ∫ t in Set.Ioi (0:ℝ), (1 + 2*t^2)^(-(5/2):ℝ) = Real.sqrt 2 / 3)
    (hC2 : ∫ t in Set.Ioi (0:ℝ), t^2*(1 + 2*t^2)^(-(7/2):ℝ) = Real.sqrt 2 / 30)
    (hC3i : IntegrableOn
      (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5/2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0)) :
    bovInt (-u) ≤ 0.046 - 0.954 * u := by
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have hGint := integrable_dom hC3i
  have hFint : Integrable (fun z : ℝ × ℝ => (Dbloch z.1 z.2 (-u)) ^ (-(5/2) : ℝ))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    integrable_blast (-u) (by nlinarith) hGint
  have hAint : Integrable (fun z : ℝ × ℝ => loA z)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    refine Integrable.mono' hGint cont_loA.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (loA_nonneg z)]
    exact loA_le z
  have hBint : Integrable (fun z : ℝ × ℝ => loB z)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    have hu2p : (0:ℝ) < 10*u^2 := by positivity
    have hscaled : Integrable (fun z : ℝ × ℝ =>
        1/(10*u^2) * (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ))
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
      hGint.const_mul (1/(10*u^2))
    refine Integrable.mono' hscaled cont_loB.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (loB_nonneg z)]
    rw [show 1/(10*u^2) * (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ)
      = (1 + 2 * z.1 ^ 2 + 2 * z.2 ^ 2) ^ (-(5/2) : ℝ) / (10*u^2) from by ring]
    rw [le_div_iff₀ hu2p]
    exact le_trans (le_of_eq (mul_comm (loB z) (10*u^2))) (lo_chain u hu2 z)
  have hHint : Integrable (fun z : ℝ × ℝ => lo u z)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    simp only [lo]
    exact hAint.add (hBint.const_mul (10*u^2))
  have hAval : ∫ z : ℝ × ℝ, loA z
      ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) = 2/9 := by
    simp only [loA]
    rw [integral_prod_mul (μ := volume.restrict (Set.Ioi 0)) (ν := volume.restrict (Set.Ioi 0))
      (f := fun t : ℝ => (1 + 2*t^2)^(-(5/2):ℝ))
      (g := fun t : ℝ => (1 + 2*t^2)^(-(5/2):ℝ))]
    rw [hC1]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hBval : ∫ z : ℝ × ℝ, loB z
      ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) = 1/450 := by
    simp only [loB]
    rw [integral_prod_mul (μ := volume.restrict (Set.Ioi 0)) (ν := volume.restrict (Set.Ioi 0))
      (f := fun t : ℝ => t^2*(1 + 2*t^2)^(-(7/2):ℝ))
      (g := fun t : ℝ => t^2*(1 + 2*t^2)^(-(7/2):ℝ))]
    rw [hC2]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hHval : ∫ z : ℝ × ℝ, lo u z
      ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) = 2/9 + u^2/45 := by
    simp only [lo]
    rw [integral_add hAint (hBint.const_mul (10*u^2)), integral_const_mul, hAval, hBval]
    ring
  have hIterGe : 2/9 + u^2/45
      ≤ ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ), (Dbloch r q (-u)) ^ (-(5/2) : ℝ) := by
    rw [integral_iter_eq (fun r q => (Dbloch r q (-u)) ^ (-(5/2) : ℝ)) hFint, ← hHval]
    exact integral_mono hHint hFint (lo_le u hu2)
  have hcoef : (0:ℝ) ≤ 12 * u / Real.pi := by positivity
  have harith := arith_main u (le_of_lt hu0)
  calc bovInt (-u)
      = (12*(-u)/Real.pi) * ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ),
          (Dbloch r q (-u)) ^ (-(5/2) : ℝ) := rfl
    _ = -((12*u/Real.pi) * ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ),
          (Dbloch r q (-u)) ^ (-(5/2) : ℝ)) := by ring
    _ ≤ -((12*u/Real.pi) * (2/9 + u^2/45)) := by
        have h2 := mul_le_mul_of_nonneg_left hIterGe hcoef
        linarith
    _ = -((12/Real.pi) * (2*u/9 + u^3/45)) := by
        field_simp
    _ ≤ -(0.954 * u - 0.046) := by linarith
    _ = 0.046 - 0.954 * u := by ring

theorem bovInt_le_linear (c : ℝ) (hc : c ∈ Set.Icc (-1) 1)
    (hC1 : ∫ t in Set.Ioi (0:ℝ), (1 + 2*t^2)^(-(5/2):ℝ) = Real.sqrt 2 / 3)
    (hC1i : IntegrableOn (fun t : ℝ => (1 + 2*t^2)^(-(5/2):ℝ)) (Set.Ioi 0))
    (hC2 : ∫ t in Set.Ioi (0:ℝ), t^2*(1 + 2*t^2)^(-(7/2):ℝ) = Real.sqrt 2 / 30)
    (hC2i : IntegrableOn (fun t : ℝ => t^2*(1 + 2*t^2)^(-(7/2):ℝ)) (Set.Ioi 0))
    (hC3 : ∫ r in Set.Ioi (0:ℝ), ∫ q in Set.Ioi (0:ℝ), (1 + 2*r^2 + 2*q^2)^(-(5/2):ℝ)
      = Real.pi/12)
    (hC3i : IntegrableOn
      (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5/2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0)) :
    bovInt c ≤ 0.046 + 0.954 * c := by
  obtain ⟨hc1, hc2⟩ := hc
  by_cases hcsign : 0 ≤ c
  · have h := bovInt_le_self (hc0 := hcsign) (hc1 := hc2) hC3 hC3i
    nlinarith
  · have hcneg : c < 0 := not_le.mp hcsign
    have hu0 : 0 < -c := by linarith
    have hu1 : -c ≤ 1 := by linarith
    have h := bovInt_neg_le (u := -c) hu0 hu1 hC1 hC2 hC3i
    rw [neg_neg] at h
    linarith

end BrickD

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology

noncomputable section
namespace Rank3Gaussian

theorem sq_mul_exp_neg_sq_le {a : ℝ} (ha : 0 < a) (u : ℝ) :
    u ^ 2 * Real.exp (-a * u ^ 2) ≤ Real.exp (-1) / a := by
  rw [le_div_iff₀ ha]
  rw [show -a * u ^ 2 = -(a * u ^ 2) from by ring]
  rw [show u ^ 2 * Real.exp (-(a * u ^ 2)) * a
      = (a * u ^ 2) * Real.exp (-(a * u ^ 2)) from by ring]
  exact mul_exp_neg_le (a * u ^ 2)

theorem integrable_exp_kernel (r q c s : ℝ) :
    Integrable (fun x : ℝ × ℝ =>
      Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)) γ2 := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ × ℝ =>
      Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)
        ≤ Real.exp 0 := Real.exp_le_exp.mpr (by
          have h1 : (0:ℝ) ≤ r ^ 2 * x.1 ^ 2 := by positivity
          have h2 : (0:ℝ) ≤ q ^ 2 * (c * x.1 + s * x.2) ^ 2 := by positivity
          linarith)
      _ = 1 := Real.exp_zero

theorem integrable_cross_kernel {r q c s : ℝ} (hr : 0 < r) (hq : 0 < q) :
    Integrable (fun x : ℝ × ℝ => x.1 * (c * x.1 + s * x.2)
      * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)) γ2 := by
  refine Integrable.mono'
    (integrable_const ((Real.exp (-1) / r ^ 2 + Real.exp (-1) / q ^ 2) / 2)) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ × ℝ => x.1 * (c * x.1 + s * x.2)
      * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)).aestronglyMeasurable
  · filter_upwards with x
    set u := x.1 with hu
    set w := c * x.1 + s * x.2 with hw
    set e := Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2) with he
    have hepos : (0:ℝ) < e := Real.exp_pos _
    have hexp_le1 : e ≤ Real.exp (-(r ^ 2 * u ^ 2)) := by
      rw [he]
      exact Real.exp_le_exp.mpr (by
        have : (0:ℝ) ≤ q ^ 2 * (c * x.1 + s * x.2) ^ 2 := by positivity
        linarith)
    have hexp_le2 : e ≤ Real.exp (-(q ^ 2 * w ^ 2)) := by
      rw [he]
      exact Real.exp_le_exp.mpr (by
        have : (0:ℝ) ≤ r ^ 2 * x.1 ^ 2 := by positivity
        linarith)
    have hAM : |u * w| ≤ (u ^ 2 + w ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|u| - |w|), sq_abs u, sq_abs w]
    have hstep : |x.1 * (c * x.1 + s * x.2)
        * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)|
        = |u * w| * e := by
      rw [show x.1 * (c * x.1 + s * x.2)
          * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)
          = (u * w) * e from by rw [hu, hw, he]]
      rw [abs_mul, abs_of_pos hepos]
    have h1 : u ^ 2 * e ≤ Real.exp (-1) / r ^ 2 :=
      calc u ^ 2 * e ≤ u ^ 2 * Real.exp (-(r ^ 2 * u ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hexp_le1 (by positivity)
        _ = u ^ 2 * Real.exp (-r ^ 2 * u ^ 2) := by rw [show -(r ^ 2 * u ^ 2) = -r ^ 2 * u ^ 2 from by ring]
        _ ≤ Real.exp (-1) / r ^ 2 := sq_mul_exp_neg_sq_le (by positivity) u
    have h2 : w ^ 2 * e ≤ Real.exp (-1) / q ^ 2 :=
      calc w ^ 2 * e ≤ w ^ 2 * Real.exp (-(q ^ 2 * w ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hexp_le2 (by positivity)
        _ = w ^ 2 * Real.exp (-q ^ 2 * w ^ 2) := by rw [show -(q ^ 2 * w ^ 2) = -q ^ 2 * w ^ 2 from by ring]
        _ ≤ Real.exp (-1) / q ^ 2 := sq_mul_exp_neg_sq_le (by positivity) w
    rw [Real.norm_eq_abs, hstep]
    calc |u * w| * e ≤ ((u ^ 2 + w ^ 2) / 2) * e := by
          exact mul_le_mul_of_nonneg_right hAM hepos.le
      _ = (u ^ 2 * e + w ^ 2 * e) / 2 := by ring
      _ ≤ (Real.exp (-1) / r ^ 2 + Real.exp (-1) / q ^ 2) / 2 := by
          have := add_le_add h1 h2
          linarith

theorem cross_kernel_prod (r q c s : ℝ) (a : Fin 3) (p : Fin 3 → ℝ × ℝ) :
    (∏ b : Fin 3, (if b = a then (p b).1 * (c * (p b).1 + s * (p b).2) else 1)
        * Real.exp (-(r ^ 2 * (p b).1 ^ 2) - q ^ 2 * (c * (p b).1 + s * (p b).2) ^ 2))
      = (p a).1 * (c * (p a).1 + s * (p a).2)
        * Real.exp (-(r ^ 2 * ∑ b, (p b).1 ^ 2)
            - q ^ 2 * ∑ b, (c * (p b).1 + s * (p b).2) ^ 2) := by
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' Finset.univ a (fun b => (p b).1 * (c * (p b).1 + s * (p b).2))]
  simp only [Finset.mem_univ, if_true]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sixdim_weighted_inner (r q c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2) (hr : 0 < r) (hq : 0 < q)
    (hcross : ∫ p : ℝ × ℝ, p.1 * (c * p.1 + s * p.2)
        * Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2) ∂γ2
      = c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 3) :
    ∫ p : Fin 3 → ℝ × ℝ, (∑ a : Fin 3, (p a).1 * zcoord c s p a)
        * Real.exp (-(r ^ 2 * ∑ a, ((p a).1) ^ 2) - q ^ 2 * ∑ a, (zcoord c s p a) ^ 2) ∂μ3
      = 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5 := by
  classical
  simp only [zcoord]
  
  have hpt : ∀ a : Fin 3,
      (fun p : Fin 3 → ℝ × ℝ => ∏ b : Fin 3,
          (if b = a then (p b).1 * (c * (p b).1 + s * (p b).2) else 1)
            * Real.exp (-(r ^ 2 * (p b).1 ^ 2) - q ^ 2 * (c * (p b).1 + s * (p b).2) ^ 2))
      = (fun p : Fin 3 → ℝ × ℝ => (p a).1 * (c * (p a).1 + s * (p a).2)
          * Real.exp (-(r ^ 2 * ∑ b, (p b).1 ^ 2)
              - q ^ 2 * ∑ b, (c * (p b).1 + s * (p b).2) ^ 2)) := by
    intro a
    funext p
    exact cross_kernel_prod r q c s a p
  
  have hIfac : ∀ a b : Fin 3, Integrable (fun x : ℝ × ℝ =>
      (if b = a then x.1 * (c * x.1 + s * x.2) else 1)
        * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)) γ2 := by
    intro a b
    by_cases h : b = a
    · have hb : (fun x : ℝ × ℝ => (if b = a then x.1 * (c * x.1 + s * x.2) else 1)
          * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2))
          = (fun x : ℝ × ℝ => x.1 * (c * x.1 + s * x.2)
            * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)) := by
        funext x
        rw [if_pos h]
      rw [hb]
      exact integrable_cross_kernel hr hq
    · have hb : (fun x : ℝ × ℝ => (if b = a then x.1 * (c * x.1 + s * x.2) else 1)
          * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2))
          = (fun x : ℝ × ℝ =>
            Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)) := by
        funext x
        rw [if_neg h, one_mul]
      rw [hb]
      exact integrable_exp_kernel r q c s
  
  have hfac : ∀ a b : Fin 3, (∫ x : ℝ × ℝ, (if b = a then x.1 * (c * x.1 + s * x.2) else 1)
        * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2) ∂γ2)
      = if b = a then c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 3
        else Real.sqrt (Dbloch r q c)⁻¹ := by
    intro a b
    by_cases h : b = a
    · have hb : (fun x : ℝ × ℝ => (if b = a then x.1 * (c * x.1 + s * x.2) else 1)
          * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2))
          = (fun x : ℝ × ℝ => x.1 * (c * x.1 + s * x.2)
            * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)) := by
        funext x
        rw [if_pos h]
      rw [hb, if_pos h]
      exact hcross
    · have hb : (fun x : ℝ × ℝ => (if b = a then x.1 * (c * x.1 + s * x.2) else 1)
          * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2))
          = (fun x : ℝ × ℝ =>
            Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2)) := by
        funext x
        rw [if_neg h, one_mul]
      rw [hb, if_neg h]
      exact bivar_laplace0 r q c s hssq hr
  
  have hterm : ∀ a : Fin 3,
      (∫ p : Fin 3 → ℝ × ℝ, (p a).1 * (c * (p a).1 + s * (p a).2)
        * Real.exp (-(r ^ 2 * ∑ b, (p b).1 ^ 2)
            - q ^ 2 * ∑ b, (c * (p b).1 + s * (p b).2) ^ 2) ∂μ3)
      = c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 3 * (Real.sqrt (Dbloch r q c)⁻¹)
        * (Real.sqrt (Dbloch r q c)⁻¹) := by
    intro a
    rw [← hpt a]
    rw [integral_fintype_prod_eq_prod (E := fun _ : Fin 3 => ℝ × ℝ) (μ := fun _ : Fin 3 => γ2)
      (f := fun b x => (if b = a then x.1 * (c * x.1 + s * x.2) else 1)
        * Real.exp (-(r ^ 2 * x.1 ^ 2) - q ^ 2 * (c * x.1 + s * x.2) ^ 2))]
    rw [Finset.prod_congr rfl (fun b _ => hfac a b)]
    rw [Fin.prod_univ_three]
    fin_cases a
    all_goals simp [mul_comm]
    all_goals ring
  
  have hsplit : (∫ p : Fin 3 → ℝ × ℝ, (∑ a : Fin 3, (p a).1 * (c * (p a).1 + s * (p a).2))
        * Real.exp (-(r ^ 2 * ∑ a, ((p a).1) ^ 2)
            - q ^ 2 * ∑ a, (c * (p a).1 + s * (p a).2) ^ 2) ∂μ3)
      = ∑ a : Fin 3, ∫ p : Fin 3 → ℝ × ℝ, (p a).1 * (c * (p a).1 + s * (p a).2)
        * Real.exp (-(r ^ 2 * ∑ b, (p b).1 ^ 2)
            - q ^ 2 * ∑ b, (c * (p b).1 + s * (p b).2) ^ 2) ∂μ3 := by
    simp only [Finset.sum_mul]
    rw [integral_finsetSum]
    intro a _
    rw [← hpt a]
    exact Integrable.fintype_prod (fun b => hIfac a b)
  rw [hsplit]
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem Dbloch_pos (r q c : ℝ) (hr : 0 < r) (hq : 0 < q) (hc : c ^ 2 ≤ 1) :
    0 < Dbloch r q c := by
  have hrq : (0:ℝ) ≤ r ^ 2 * q ^ 2 := by positivity
  have hprod : (0:ℝ) ≤ r ^ 2 * q ^ 2 * (1 - c ^ 2) :=
    mul_nonneg hrq (by linarith)
  have hval : (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) - 4 * r ^ 2 * q ^ 2
      = 1 + 2 * r ^ 2 + 2 * q ^ 2 := by ring
  unfold Dbloch
  nlinarith

theorem sqrt_inv_pow_eq_rpow {D : ℝ} (hD : 0 < D) (n : ℕ) :
    Real.sqrt (D⁻¹) ^ n = D ^ (-(n:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, Real.inv_rpow hD.le, ← Real.rpow_neg hD.le]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
  congr 1

  ring

theorem sqrt_inv_pow_five_eq_rpow {D : ℝ} (hD : 0 < D) :
    Real.sqrt (D⁻¹) ^ 5 = D ^ (-(5/2) : ℝ) := by
  rw [sqrt_inv_pow_eq_rpow hD 5]
  norm_num

end Rank3Gaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1000000
namespace Rank3Gaussian

abbrev b2nu : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))

abbrev b2nu2 : Measure (ℝ × ℝ) := b2nu.prod b2nu

def b2Sx (p : Fin 3 → ℝ × ℝ) : ℝ := ∑ a, (p a).1 ^ 2

def b2Sz (c s : ℝ) (p : Fin 3 → ℝ × ℝ) : ℝ := ∑ a, (zcoord c s p a) ^ 2

def b2In (c s : ℝ) (p : Fin 3 → ℝ × ℝ) : ℝ := ∑ a, (p a).1 * zcoord c s p a

def b2F (c s : ℝ) (p : Fin 3 → ℝ × ℝ) (r q : ℝ) : ℝ :=
  b2In c s p * Real.exp (-(r ^ 2 * b2Sx p) - q ^ 2 * b2Sz c s p)

def b2G (c s : ℝ) (p : Fin 3 → ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a) *
    (Real.exp (-(z.1 ^ 2 * b2Sx p)) * Real.exp (-(z.2 ^ 2 * b2Sz c s p)))

lemma b2Sx_nonneg (p : Fin 3 → ℝ × ℝ) : 0 ≤ b2Sx p :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

lemma b2Sz_nonneg (c s : ℝ) (p : Fin 3 → ℝ × ℝ) : 0 ≤ b2Sz c s p :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

lemma b2Sx_eq_zero_iff (p : Fin 3 → ℝ × ℝ) : b2Sx p = 0 ↔ ∀ a, (p a).1 = 0 := by
  rw [b2Sx, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((p i).1))]
  simp [sq_eq_zero_iff]

lemma b2Sz_eq_zero_iff (c s : ℝ) (p : Fin 3 → ℝ × ℝ) :
    b2Sz c s p = 0 ↔ ∀ a, zcoord c s p a = 0 := by
  rw [b2Sz, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (zcoord c s p i))]
  simp [sq_eq_zero_iff]

lemma b2_nrmX_eq (p : Fin 3 → ℝ × ℝ) :
    nrm3 (fun a => (p a).1) = Real.sqrt (b2Sx p) := rfl

lemma b2_nrmZ_eq (c s : ℝ) (p : Fin 3 → ℝ × ℝ) :
    nrm3 (fun a => zcoord c s p a) = Real.sqrt (b2Sz c s p) := rfl

lemma b2_nrmX_nonneg (p : Fin 3 → ℝ × ℝ) : 0 ≤ nrm3 (fun a => (p a).1) := by
  rw [b2_nrmX_eq]
  exact Real.sqrt_nonneg _

lemma b2_nrmZ_nonneg (c s : ℝ) (p : Fin 3 → ℝ × ℝ) :
    0 ≤ nrm3 (fun a => zcoord c s p a) := by
  rw [b2_nrmZ_eq]
  exact Real.sqrt_nonneg _

lemma b2_abs_in_le (c s : ℝ) (p : Fin 3 → ℝ × ℝ) :
    |b2In c s p| ≤ nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a) := by
  have hcs : (b2In c s p) ^ 2 ≤ b2Sx p * b2Sz c s p := by
    simpa [b2In, b2Sx, b2Sz] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
        (fun a => (p a).1) (fun a => zcoord c s p a))
  calc |b2In c s p| = Real.sqrt ((b2In c s p) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (b2Sx p * b2Sz c s p) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p) :=
      Real.sqrt_mul (b2Sx_nonneg p) (b2Sz c s p)
    _ = nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a) := rfl

lemma b2_integral_exp_neg_sq_mul_Ioi (a : ℝ) (ha : 0 < a) :
    ∫ r in Set.Ioi (0 : ℝ), Real.exp (-(r ^ 2 * a))
      = Real.sqrt Real.pi / (2 * Real.sqrt a) := by
  have h2 : ∀ x : ℝ, Real.exp (-(x ^ 2 * a)) = Real.exp (-a * x ^ 2) := by
    intro x
    rw [show -(x ^ 2 * a) = -a * x ^ 2 from by ring]
  simp_rw [h2]
  rw [integral_gaussian_Ioi, Real.sqrt_div Real.pi_pos.le]
  ring

lemma b2_lintegral_exp_neg_sq_mul_Ioi (a : ℝ) (ha : 0 < a) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(r ^ 2 * a)))
      = ENNReal.ofReal (Real.sqrt Real.pi / (2 * Real.sqrt a)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [b2_integral_exp_neg_sq_mul_Ioi a ha]
  · have h : (fun r : ℝ => Real.exp (-(r ^ 2 * a))) = fun r => Real.exp (-a * r ^ 2) := by
      funext x
      rw [show -(x ^ 2 * a) = -a * x ^ 2 from by ring]
    rw [h]
    exact (integrable_exp_neg_mul_sq ha).integrableOn
  · filter_upwards with r using Real.exp_nonneg _

lemma b2_measure_xnull : μ3 {p : Fin 3 → ℝ × ℝ | b2Sx p = 0} = 0 := by
  haveI : NullSingletonClass (gaussianReal (0 : ℝ) 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hset : {p : Fin 3 → ℝ × ℝ | b2Sx p = 0}
      = Set.pi Set.univ (fun _ : Fin 3 => {q : ℝ × ℝ | q.1 = 0}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.pi, Set.mem_univ, forall_true_left,
      b2Sx_eq_zero_iff]
  rw [hset, μ3, Measure.pi_pi]
  have hγ : γ2 ({q : ℝ × ℝ | q.1 = 0}) = 0 := by
    have hset2 : ({q : ℝ × ℝ | q.1 = 0}) = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext q
      simp [Set.mem_prod, eq_comm]
    rw [hset2, γ2, Measure.prod_prod, measure_singleton]
    simp
  simp [hγ]

lemma b2_measure_znull (c s : ℝ) (hcs : c ≠ 0 ∨ s ≠ 0) :
    μ3 {p : Fin 3 → ℝ × ℝ | b2Sz c s p = 0} = 0 := by
  haveI : NullSingletonClass (gaussianReal (0 : ℝ) 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hset : {p : Fin 3 → ℝ × ℝ | b2Sz c s p = 0}
      = Set.pi Set.univ (fun _ : Fin 3 => {q : ℝ × ℝ | c * q.1 + s * q.2 = 0}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.pi, Set.mem_univ, forall_true_left,
      b2Sz_eq_zero_iff, zcoord]
  rw [hset, μ3, Measure.pi_pi]
  have hγ : γ2 ({q : ℝ × ℝ | c * q.1 + s * q.2 = 0}) = 0 := by
    have hmeas : MeasurableSet {q : ℝ × ℝ | c * q.1 + s * q.2 = 0} :=
      isClosed_eq (by continuity) (by continuity) |>.measurableSet
    rcases eq_or_ne s 0 with hs | hs
    · have hc : c ≠ 0 := by rcases hcs with h | h; exacts [h, absurd hs h]
      have hset2 : {q : ℝ × ℝ | c * q.1 + s * q.2 = 0}
          = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
        subst hs
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ,
          and_true]
        constructor
        · intro h
          have h' : c * q.1 = 0 := by simpa using h
          exact (mul_eq_zero.mp h').resolve_left hc
        · intro h
          rw [h]
          ring
      rw [hset2, γ2, Measure.prod_prod, measure_singleton]
      simp
    · rw [γ2, Measure.prod_apply hmeas]
      have hzero : ∀ x : ℝ, (gaussianReal 0 1) {a : ℝ | c * x + s * a = 0} = 0 := by
        intro x
        have hsub : ({a : ℝ | c * x + s * a = 0}).Subsingleton := by
          intro y1 hy1 y2 hy2
          simp only [Set.mem_setOf_eq] at hy1 hy2
          have hxy : s * y1 = s * y2 := by linarith
          exact mul_left_cancel₀ hs hxy
        exact hsub.measure_zero _
      simp only [Set.preimage_setOf_eq]
      simp [hzero]
  simp [hγ]

lemma b2_ae_good (c s : ℝ) (hcs : c ≠ 0 ∨ s ≠ 0) :
    ∀ᵐ p ∂μ3, b2Sx p ≠ 0 ∧ b2Sz c s p ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hset : {p : Fin 3 → ℝ × ℝ | ¬(b2Sx p ≠ 0 ∧ b2Sz c s p ≠ 0)}
      = {p | b2Sx p = 0} ∪ {p | b2Sz c s p = 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, ne_eq, not_and_or, not_not]
  rw [hset]
  exact measure_union_null_iff.mpr ⟨b2_measure_xnull, b2_measure_znull c s hcs⟩

lemma b2_scalar_identity (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Real.sqrt Real.pi / (2 * Real.sqrt A) * (Real.sqrt Real.pi / (2 * Real.sqrt B))
      = Real.pi / 4 * (Real.sqrt A * Real.sqrt B)⁻¹ := by
  have hA' : Real.sqrt A ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hB' : Real.sqrt B ≠ 0 := (Real.sqrt_pos.2 hB).ne'
  have hp2 : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  rw [sq, hp2]
  ring

lemma b2_laplace_pair (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∫ z : ℝ × ℝ, (fun r => Real.exp (-(r ^ 2 * A))) z.1
        * (fun q => Real.exp (-(q ^ 2 * B))) z.2 ∂b2nu2
      = Real.sqrt Real.pi / (2 * Real.sqrt A) * (Real.sqrt Real.pi / (2 * Real.sqrt B)) := by
  rw [show ∫ z : ℝ × ℝ, (fun r => Real.exp (-(r ^ 2 * A))) z.1
        * (fun q => Real.exp (-(q ^ 2 * B))) z.2 ∂b2nu2
      = (∫ r, Real.exp (-(r ^ 2 * A)) ∂b2nu) * (∫ q, Real.exp (-(q ^ 2 * B)) ∂b2nu)
      from integral_prod_mul (μ := b2nu) (ν := b2nu)
        (fun r => Real.exp (-(r ^ 2 * A))) (fun q => Real.exp (-(q ^ 2 * B)))]
  rw [b2_integral_exp_neg_sq_mul_Ioi A hA, b2_integral_exp_neg_sq_mul_Ioi B hB]

lemma b2_pointwise (c s : ℝ) (p : Fin 3 → ℝ × ℝ)
    (hSx : 0 < b2Sx p) (hSz : 0 < b2Sz c s p) :
    b2In c s p * (nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a))⁻¹
      = (4 / Real.pi) * ∫ z : ℝ × ℝ, b2F c s p z.1 z.2 ∂b2nu2 := by
  have hexp : ∀ z : ℝ × ℝ, b2F c s p z.1 z.2
      = b2In c s p * ((fun r => Real.exp (-(r ^ 2 * b2Sx p))) z.1
          * (fun q => Real.exp (-(q ^ 2 * b2Sz c s p))) z.2) := by
    intro z
    rw [b2F, show -(z.1 ^ 2 * b2Sx p) - z.2 ^ 2 * b2Sz c s p
      = -(z.1 ^ 2 * b2Sx p) + -(z.2 ^ 2 * b2Sz c s p) from by ring, Real.exp_add]
  simp_rw [hexp]
  rw [integral_const_mul]
  rw [b2_laplace_pair (b2Sx p) (b2Sz c s p) hSx hSz,
    b2_scalar_identity (b2Sx p) (b2Sz c s p) hSx hSz, b2_nrmX_eq, b2_nrmZ_eq]
  have key : (4 / Real.pi) * (Real.pi / 4) = 1 := by field_simp
  calc b2In c s p * (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))⁻¹
      = (4 / Real.pi * (Real.pi / 4))
          * (b2In c s p * (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))⁻¹) := by
        rw [key, one_mul]
    _ = (4 / Real.pi)
          * (b2In c s p * (Real.pi / 4 * (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))⁻¹)) := by
        ring

lemma measurable_zcoord (c s : ℝ) (a : Fin 3) :
    Measurable fun p : Fin 3 → ℝ × ℝ => zcoord c s p a := by
  have h : (fun p : Fin 3 → ℝ × ℝ => zcoord c s p a)
      = fun p => c * (p a).1 + s * (p a).2 := rfl
  rw [h]
  exact (measurable_fst.comp (measurable_pi_apply a)).const_mul c |>.add
    ((measurable_snd.comp (measurable_pi_apply a)).const_mul s)

lemma measurable_b2Sx : Measurable fun p : Fin 3 → ℝ × ℝ => b2Sx p := by
  have h : (fun p : Fin 3 → ℝ × ℝ => b2Sx p) = fun p => ∑ a, (p a).1 ^ 2 := rfl
  rw [h]
  exact Finset.measurable_sum _ (fun a _ =>
    (measurable_fst.comp (measurable_pi_apply a)).pow measurable_const)

lemma measurable_b2Sz (c s : ℝ) : Measurable fun p : Fin 3 → ℝ × ℝ => b2Sz c s p := by
  have h : (fun p : Fin 3 → ℝ × ℝ => b2Sz c s p) = fun p => ∑ a, zcoord c s p a ^ 2 := rfl
  rw [h]
  exact Finset.measurable_sum _ (fun a _ => (measurable_zcoord c s a).pow measurable_const)

lemma measurable_b2In (c s : ℝ) : Measurable fun p : Fin 3 → ℝ × ℝ => b2In c s p := by
  have h : (fun p : Fin 3 → ℝ × ℝ => b2In c s p)
      = fun p => ∑ a, (p a).1 * zcoord c s p a := rfl
  rw [h]
  exact Finset.measurable_sum _ (fun a _ =>
    (measurable_fst.comp (measurable_pi_apply a)).mul (measurable_zcoord c s a))

lemma measurable_b2nrmX :
    Measurable fun p : Fin 3 → ℝ × ℝ => nrm3 (fun a => (p a).1) := by
  have h : (fun p : Fin 3 → ℝ × ℝ => nrm3 (fun a => (p a).1))
      = fun p => Real.sqrt (b2Sx p) := rfl
  rw [h]
  exact Real.continuous_sqrt.measurable.comp measurable_b2Sx

lemma measurable_b2nrmZ (c s : ℝ) :
    Measurable fun p : Fin 3 → ℝ × ℝ => nrm3 (fun a => zcoord c s p a) := by
  have h : (fun p : Fin 3 → ℝ × ℝ => nrm3 (fun a => zcoord c s p a))
      = fun p => Real.sqrt (b2Sz c s p) := rfl
  rw [h]
  exact Real.continuous_sqrt.measurable.comp (measurable_b2Sz c s)

lemma measurable_b2G (c s : ℝ) :
    Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2G c s pz.1 pz.2 := by
  have hSx : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2Sx pz.1 :=
    measurable_b2Sx.comp measurable_fst
  have hSz : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2Sz c s pz.1 :=
    (measurable_b2Sz c s).comp measurable_fst
  have hX : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) =>
      nrm3 (fun a => (pz.1 a).1) := measurable_b2nrmX.comp measurable_fst
  have hZ : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) =>
      nrm3 (fun a => zcoord c s pz.1 a) := (measurable_b2nrmZ c s).comp measurable_fst
  have hr : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => pz.2.1 := measurable_snd.fst
  have hq : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => pz.2.2 := measurable_snd.snd
  have h1 : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (-(pz.2.1 ^ 2 * b2Sx pz.1)) :=
    Real.measurable_exp.comp (((hr.pow measurable_const).mul hSx).neg)
  have h2 : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (-(pz.2.2 ^ 2 * b2Sz c s pz.1)) :=
    Real.measurable_exp.comp (((hq.pow measurable_const).mul hSz).neg)
  exact (hX.mul hZ).mul (h1.mul h2)

lemma measurable_b2F (c s : ℝ) :
    Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2F c s pz.1 pz.2.1 pz.2.2 := by
  have hIn : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2In c s pz.1 :=
    (measurable_b2In c s).comp measurable_fst
  have hSx : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2Sx pz.1 :=
    measurable_b2Sx.comp measurable_fst
  have hSz : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2Sz c s pz.1 :=
    (measurable_b2Sz c s).comp measurable_fst
  have hr : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => pz.2.1 := measurable_snd.fst
  have hq : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => pz.2.2 := measurable_snd.snd
  have hexp : Measurable fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (-(pz.2.1 ^ 2 * b2Sx pz.1) - pz.2.2 ^ 2 * b2Sz c s pz.1) :=
    Real.measurable_exp.comp
      (((hr.pow measurable_const).mul hSx).neg.sub ((hq.pow measurable_const).mul hSz))
  exact hIn.mul hexp

lemma b2G_nonneg (c s : ℝ) (p : Fin 3 → ℝ × ℝ) (z : ℝ × ℝ) : 0 ≤ b2G c s p z := by
  rw [b2G]
  exact mul_nonneg (mul_nonneg (b2_nrmX_nonneg p) (b2_nrmZ_nonneg c s p))
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))

lemma b2_abs_F_le_G (c s : ℝ) (p : Fin 3 → ℝ × ℝ) (r q : ℝ) :
    ‖b2F c s p r q‖ ≤ nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a) *
      (Real.exp (-(r ^ 2 * b2Sx p)) * Real.exp (-(q ^ 2 * b2Sz c s p))) := by
  rw [Real.norm_eq_abs, b2F, show -(r ^ 2 * b2Sx p) - q ^ 2 * b2Sz c s p
      = -(r ^ 2 * b2Sx p) + -(q ^ 2 * b2Sz c s p) from by ring, Real.exp_add,
    abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤
      Real.exp (-(r ^ 2 * b2Sx p)) * Real.exp (-(q ^ 2 * b2Sz c s p)))]
  exact mul_le_mul_of_nonneg_right (b2_abs_in_le c s p) (by positivity)

lemma b2_lintegral_G_inner_eq (c s : ℝ) (p : Fin 3 → ℝ × ℝ)
    (hSx : 0 < b2Sx p) (hSz : 0 < b2Sz c s p) :
    ∫⁻ z : ℝ × ℝ, ‖b2G c s p z‖ₑ ∂b2nu2 = ENNReal.ofReal (Real.pi / 4) := by
  have hpt : ∀ z : ℝ × ℝ, ‖b2G c s p z‖ₑ
      = ENNReal.ofReal (nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a))
        * ((fun r => ENNReal.ofReal (Real.exp (-(r ^ 2 * b2Sx p)))) z.1
            * (fun q => ENNReal.ofReal (Real.exp (-(q ^ 2 * b2Sz c s p)))) z.2) := by
    intro z
    rw [Real.enorm_of_nonneg (b2G_nonneg c s p z), b2G,
      ENNReal.ofReal_mul (mul_nonneg (b2_nrmX_nonneg p) (b2_nrmZ_nonneg c s p)),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.exp (-(z.1 ^ 2 * b2Sx p)))]
  have hfac : ∫⁻ a : ℝ × ℝ, (fun r => ENNReal.ofReal (Real.exp (-(r ^ 2 * b2Sx p)))) a.1
        * (fun q => ENNReal.ofReal (Real.exp (-(q ^ 2 * b2Sz c s p)))) a.2 ∂b2nu2
      = (∫⁻ r, ENNReal.ofReal (Real.exp (-(r ^ 2 * b2Sx p))) ∂b2nu)
        * (∫⁻ q, ENNReal.ofReal (Real.exp (-(q ^ 2 * b2Sz c s p))) ∂b2nu) :=
    lintegral_prod_mul (f := fun r => ENNReal.ofReal (Real.exp (-(r ^ 2 * b2Sx p))))
      (g := fun q => ENNReal.ofReal (Real.exp (-(q ^ 2 * b2Sz c s p))))
      (by measurability) (by measurability)
  calc ∫⁻ z : ℝ × ℝ, ‖b2G c s p z‖ₑ ∂b2nu2
      = ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (nrm3 (fun a => (p a).1) *
            nrm3 (fun a => zcoord c s p a))
          * ((fun r => ENNReal.ofReal (Real.exp (-(r ^ 2 * b2Sx p)))) z.1
              * (fun q => ENNReal.ofReal (Real.exp (-(q ^ 2 * b2Sz c s p)))) z.2) ∂b2nu2 := by
        simp_rw [hpt]
    _ = ENNReal.ofReal (nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a))
          * ∫⁻ a : ℝ × ℝ, (fun r => ENNReal.ofReal (Real.exp (-(r ^ 2 * b2Sx p)))) a.1
              * (fun q => ENNReal.ofReal (Real.exp (-(q ^ 2 * b2Sz c s p)))) a.2 ∂b2nu2 :=
        lintegral_const_mul _ (by measurability)
    _ = ENNReal.ofReal (nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a))
          * ((∫⁻ r, ENNReal.ofReal (Real.exp (-(r ^ 2 * b2Sx p))) ∂b2nu)
              * (∫⁻ q, ENNReal.ofReal (Real.exp (-(q ^ 2 * b2Sz c s p))) ∂b2nu)) :=
        congrArg _ hfac
    _ = ENNReal.ofReal (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))
          * ((ENNReal.ofReal (Real.sqrt Real.pi / (2 * Real.sqrt (b2Sx p))))
              * (ENNReal.ofReal (Real.sqrt Real.pi / (2 * Real.sqrt (b2Sz c s p))))) := by
        rw [b2_lintegral_exp_neg_sq_mul_Ioi (b2Sx p) hSx,
          b2_lintegral_exp_neg_sq_mul_Ioi (b2Sz c s p) hSz, b2_nrmX_eq, b2_nrmZ_eq]
    _ = ENNReal.ofReal (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))
          * ENNReal.ofReal (Real.sqrt Real.pi / (2 * Real.sqrt (b2Sx p))
              * (Real.sqrt Real.pi / (2 * Real.sqrt (b2Sz c s p)))) := by
        rw [← ENNReal.ofReal_mul
          (by positivity : (0:ℝ) ≤ Real.sqrt Real.pi / (2 * Real.sqrt (b2Sx p)))]
    _ = ENNReal.ofReal (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))
          * ENNReal.ofReal (Real.pi / 4
              * (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))⁻¹) := by
        rw [b2_scalar_identity (b2Sx p) (b2Sz c s p) hSx hSz]
    _ = ENNReal.ofReal (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p)
          * (Real.pi / 4 * (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))⁻¹)) := by
        rw [← ENNReal.ofReal_mul
          (by positivity : (0:ℝ) ≤ Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))]
    _ = ENNReal.ofReal (Real.pi / 4) := by
        rw [show Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p)
            * (Real.pi / 4 * (Real.sqrt (b2Sx p) * Real.sqrt (b2Sz c s p))⁻¹)
            = Real.pi / 4 from by field_simp]

lemma b2_lintegral_G_inner_le (c s : ℝ) (p : Fin 3 → ℝ × ℝ) :
    ∫⁻ z : ℝ × ℝ, ‖b2G c s p z‖ₑ ∂b2nu2 ≤ ENNReal.ofReal (Real.pi / 4) := by
  rcases eq_or_lt_of_le (b2Sx_nonneg p) with hSx | hSx
  · have hzero : ∀ z : ℝ × ℝ, b2G c s p z = 0 := by
      intro z
      have h0 : nrm3 (fun a => (p a).1) = 0 := by
        rw [b2_nrmX_eq, ← hSx, Real.sqrt_zero]
      rw [b2G, h0, zero_mul, zero_mul]
    simp only [hzero, enorm_zero]
    rw [lintegral_zero]
    exact zero_le
  · rcases eq_or_lt_of_le (b2Sz_nonneg c s p) with hSz | hSz
    · have hzero : ∀ z : ℝ × ℝ, b2G c s p z = 0 := by
        intro z
        have h0 : nrm3 (fun a => zcoord c s p a) = 0 := by
          rw [b2_nrmZ_eq, ← hSz, Real.sqrt_zero]
        rw [b2G, h0, mul_zero, zero_mul]
      simp only [hzero, enorm_zero]
      rw [lintegral_zero]
      exact zero_le
    · exact le_of_eq (b2_lintegral_G_inner_eq c s p hSx hSz)

lemma b2_integrable_G (c s : ℝ) :
    Integrable (fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2G c s pz.1 pz.2)
      (μ3.prod b2nu2) := by
  refine ⟨(measurable_b2G c s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ pz, ‖b2G c s pz.1 pz.2‖ₑ ∂(μ3.prod b2nu2)
      = ∫⁻ p, ∫⁻ z, ‖b2G c s p z‖ₑ ∂b2nu2 ∂μ3 :=
        lintegral_prod _ (measurable_b2G c s).enorm.aemeasurable
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.pi / 4) ∂μ3 :=
        lintegral_mono (fun p => b2_lintegral_G_inner_le c s p)
    _ = ENNReal.ofReal (Real.pi / 4) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ < ⊤ := ENNReal.ofReal_lt_top

lemma b2_integrable_F (c s : ℝ) :
    Integrable (fun pz : (Fin 3 → ℝ × ℝ) × (ℝ × ℝ) => b2F c s pz.1 pz.2.1 pz.2.2)
      (μ3.prod b2nu2) := by
  refine Integrable.mono' (b2_integrable_G c s) (measurable_b2F c s).aestronglyMeasurable ?_
  filter_upwards with pz
  exact b2_abs_F_le_G c s pz.1 pz.2.1 pz.2.2

lemma b2_sqrt_inv_pow (x : ℝ) (hx : 0 < x) :
    (Real.sqrt x⁻¹) ^ 5 = x ^ (-(5 / 2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le,
    ← Real.rpow_natCast (x ^ (-(1 / 2))) 5, ← Real.rpow_mul hx.le]
  norm_num

lemma b2_Dbloch_pos (c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2) (r q : ℝ)
    (hr : 0 < r) (hq : 0 < q) : 0 < Dbloch r q c := by
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have hr2 : (0:ℝ) ≤ r ^ 2 := sq_nonneg r
  have hq2 : (0:ℝ) ≤ q ^ 2 := sq_nonneg q
  have hkey : 4 * c ^ 2 * r ^ 2 * q ^ 2 ≤ 4 * r ^ 2 * q ^ 2 := by
    have h1 : c ^ 2 * (r ^ 2 * q ^ 2) ≤ 1 * (r ^ 2 * q ^ 2) :=
      mul_le_mul_of_nonneg_right hc2 (mul_nonneg hr2 hq2)
    nlinarith [h1]
  rw [Dbloch]
  nlinarith [hkey]

lemma b2_double_const (k : ℝ) (f : ℝ → ℝ → ℝ) :
    ∫ r, ∫ q, k * f r q ∂b2nu ∂b2nu = k * ∫ r, ∫ q, f r q ∂b2nu ∂b2nu := by
  rw [show (fun r => ∫ q, k * f r q ∂b2nu) = (fun r => k * ∫ q, f r q ∂b2nu) from
    funext fun r => integral_const_mul _ _]
  exact integral_const_mul _ _

lemma b2_const_alg (c X : ℝ) : (4 / Real.pi) * (3 * c * X) = (12 * c / Real.pi) * X := by
  field_simp
  ring

lemma b2_key_ae (c s : ℝ) (hcs : c ≠ 0 ∨ s ≠ 0) :
    ∀ᵐ p ∂μ3, innerQ (fun a => (p a).1) (fun a => zcoord c s p a)
      = (4 / Real.pi) * ∫ z : ℝ × ℝ, b2F c s p z.1 z.2 ∂b2nu2 := by
  filter_upwards [b2_ae_good c s hcs] with p hp
  have hSx : 0 < b2Sx p := lt_of_le_of_ne (b2Sx_nonneg p) (Ne.symm hp.1)
  have hSz : 0 < b2Sz c s p := lt_of_le_of_ne (b2Sz_nonneg c s p) (Ne.symm hp.2)
  have hcond : ¬(nrm3 (fun a => (p a).1) = 0 ∨ nrm3 (fun a => zcoord c s p a) = 0) := by
    rintro (h | h)
    · exact hp.1 ((Real.sqrt_eq_zero (b2Sx_nonneg p)).mp (by rwa [b2_nrmX_eq] at h))
    · exact hp.2 ((Real.sqrt_eq_zero (b2Sz_nonneg c s p)).mp (by rwa [b2_nrmZ_eq] at h))
  rw [innerQ, if_neg hcond, div_eq_mul_inv]
  exact b2_pointwise c s p hSx hSz

lemma b2_swap (c s : ℝ) :
    ∫ p, (∫ z : ℝ × ℝ, b2F c s p z.1 z.2 ∂b2nu2) ∂μ3
      = ∫ z : ℝ × ℝ, (∫ p, b2F c s p z.1 z.2 ∂μ3) ∂b2nu2 :=
  integral_integral_swap (α := Fin 3 → ℝ × ℝ) (β := ℝ × ℝ) (E := ℝ)
    (μ := μ3) (ν := b2nu2) (f := fun p z => b2F c s p z.1 z.2) (b2_integrable_F c s)

lemma b2_prod (c s : ℝ) :
    ∫ z : ℝ × ℝ, (∫ p : Fin 3 → ℝ × ℝ, b2F c s p z.1 z.2 ∂μ3) ∂b2nu2
      = ∫ r, ∫ q, (∫ p : Fin 3 → ℝ × ℝ, b2F c s p r q ∂μ3) ∂b2nu ∂b2nu :=
  integral_prod (α := ℝ) (β := ℝ) (E := ℝ) (μ := b2nu) (ν := b2nu)
    (f := fun z : ℝ × ℝ => ∫ p : Fin 3 → ℝ × ℝ, b2F c s p z.1 z.2 ∂μ3)
    (b2_integrable_F c s).integral_prod_right

lemma b2_six (c s : ℝ)
    (h6' : ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : Fin 3 → ℝ × ℝ, b2F c s p r q ∂μ3
        = 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5) :
    ∫ r, ∫ q, (∫ p, b2F c s p r q ∂μ3) ∂b2nu ∂b2nu
      = ∫ r, ∫ q, 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5 ∂b2nu ∂b2nu := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact h6' r q hr hq

lemma b2_fin (c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2) :
    ∫ r, ∫ q, 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5 ∂b2nu ∂b2nu
      = 3 * c * ∫ r, ∫ q, (Dbloch r q c) ^ (-(5 / 2) : ℝ) ∂b2nu ∂b2nu := by
  refine Eq.trans (b2_double_const (3 * c) (fun r q => (Real.sqrt (Dbloch r q c)⁻¹) ^ 5)) ?_
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact b2_sqrt_inv_pow (Dbloch r q c) (b2_Dbloch_pos c s hssq r q hr hq)

theorem bov_expectation_eq_bovInt (c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2)
    (h6 : ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : Fin 3 → ℝ × ℝ, (∑ a, (p a).1 * zcoord c s p a)
          * Real.exp (-(r ^ 2 * ∑ a, ((p a).1) ^ 2) - q ^ 2 * ∑ a, (zcoord c s p a) ^ 2) ∂μ3
        = 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5) :
    ∫ p : Fin 3 → ℝ × ℝ, innerQ (fun a => (p a).1) (fun a => zcoord c s p a) ∂μ3
      = bovInt c := by
  have hcs : c ≠ 0 ∨ s ≠ 0 := by
    rcases eq_or_ne c 0 with hc | hc
    · rw [hc] at hssq
      right
      intro hs
      rw [hs] at hssq
      norm_num at hssq
    · exact Or.inl hc
  have h6' : ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : Fin 3 → ℝ × ℝ, b2F c s p r q ∂μ3
        = 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5 := by
    intro r q hr hq
    simpa only [b2F, b2In, b2Sx, b2Sz] using h6 r q hr hq
  calc ∫ p : Fin 3 → ℝ × ℝ, innerQ (fun a => (p a).1) (fun a => zcoord c s p a) ∂μ3
      = ∫ p, (4 / Real.pi) * (∫ z : ℝ × ℝ, b2F c s p z.1 z.2 ∂b2nu2) ∂μ3 :=
        integral_congr_ae (b2_key_ae c s hcs)
    _ = (4 / Real.pi) * ∫ p, (∫ z : ℝ × ℝ, b2F c s p z.1 z.2 ∂b2nu2) ∂μ3 :=
        integral_const_mul _ _
    _ = (4 / Real.pi) * ∫ z : ℝ × ℝ, (∫ p, b2F c s p z.1 z.2 ∂μ3) ∂b2nu2 :=
        congrArg (fun t => (4 / Real.pi) * t) (b2_swap c s)
    _ = (4 / Real.pi) * ∫ r, ∫ q, (∫ p, b2F c s p r q ∂μ3) ∂b2nu ∂b2nu :=
        congrArg (fun t => (4 / Real.pi) * t) (b2_prod c s)
    _ = (4 / Real.pi) * ∫ r, ∫ q, 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5
          ∂b2nu ∂b2nu :=
        congrArg (fun t => (4 / Real.pi) * t) (b2_six c s h6')
    _ = (4 / Real.pi) * (3 * c * ∫ r, ∫ q, (Dbloch r q c) ^ (-(5 / 2) : ℝ)
          ∂b2nu ∂b2nu) :=
        congrArg (fun t => (4 / Real.pi) * t) (b2_fin c s hssq)
    _ = bovInt c := by
        rw [bovInt]
        exact b2_const_alg c _

end Rank3Gaussian

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal Real InnerProductSpace BigOperators

namespace BrickE

noncomputable def toEuclideanCLM' {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

lemma toEuclideanCLM'_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    toEuclideanCLM' M v = Matrix.toEuclideanLin M v := rfl

lemma toEuclideanCLM'_eq (M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ) :
    toEuclideanCLM' M = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3 × Fin 2) M := by
  refine ContinuousLinearMap.ext fun v => ?_
  show Matrix.toEuclideanLin M v = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3 × Fin 2) M v
  exact (LinearMap.congr_fun (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M) v).symm

lemma ofLp_toEuclideanLin {m n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    (Matrix.toEuclideanLin M v).ofLp = M *ᵥ v.ofLp := rfl

lemma psiMat_apply (c s : ℝ) (a b : Fin 3) (p q : Fin 2) :
    Rank3Gaussian.psiMat c s (a, p) (b, q) =
      if a = b then (!![(1 : ℝ), 0; c, s]) p q else 0 := by
  unfold Rank3Gaussian.psiMat
  rw [Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    fin_cases p <;> fin_cases q <;> simp
  · simp [hab]

theorem psiMat_mulVec_pair (c s : ℝ) (w : Fin 3 × Fin 2 → ℝ) (a : Fin 3) :
    (Rank3Gaussian.psiMat c s *ᵥ w) (a, 0) = w (a, 0) ∧
      (Rank3Gaussian.psiMat c s *ᵥ w) (a, 1) = c * w (a, 0) + s * w (a, 1) := by
  have key : ∀ q : Fin 2, (Rank3Gaussian.psiMat c s *ᵥ w) (a, q)
      = ∑ p : Fin 2, Rank3Gaussian.psiMat c s (a, q) (a, p) * w (a, p) := by
    intro q
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_eq_single a ?_ ?_
    · intro b _ hne
      have hzero : ∀ p : Fin 2, Rank3Gaussian.psiMat c s (a, q) (b, p) * w (b, p) = 0 := by
        intro p
        rw [psiMat_apply, if_neg (by intro h; exact hne h.symm), zero_mul]
      simp only [hzero, Finset.sum_const_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  constructor
  · rw [key 0, Fin.sum_univ_two]
    simp [psiMat_apply]
  · rw [key 1, Fin.sum_univ_two]
    simp only [psiMat_apply, if_true]
    norm_num

lemma vecMul_psiMat (c s : ℝ) (t : Fin 3 × Fin 2 → ℝ) (r : Fin 3 × Fin 2) :
    (t ᵥ* Rank3Gaussian.psiMat c s) r =
      if r.2 = 0 then t (r.1, 0) + c * t (r.1, 1) else s * t (r.1, 1) := by
  obtain ⟨b, q⟩ := r
  rw [Matrix.vecMul_eq_sum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  have h : ∑ a : Fin 3, (∑ p : Fin 2, t (a, p) * Rank3Gaussian.psiMat c s (a, p) (b, q))
      = ∑ p : Fin 2, t (b, p) * Rank3Gaussian.psiMat c s (b, p) (b, q) := by
    refine Finset.sum_eq_single b ?_ ?_
    · intro a _ hne
      have hzero : ∀ p : Fin 2, t (a, p) * Rank3Gaussian.psiMat c s (a, p) (b, q) = 0 := by
        intro p
        rw [psiMat_apply]
        simp [hne]
      simp only [hzero, Finset.sum_const_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  rw [h, Fin.sum_univ_two]
  fin_cases q <;> simp [psiMat_apply] <;> ring

lemma vecMul_phiMat {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (t : Fin 3 × Fin 2 → ℝ) (r : Fin 3 × Fin n) :
    (t ᵥ* Rank3Gaussian.phiMat u v) r = t (r.1, 0) * u.ofLp r.2 + t (r.1, 1) * v.ofLp r.2 := by
  obtain ⟨b, k⟩ := r
  rw [Matrix.vecMul_eq_sum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  have h : ∑ a : Fin 3, (∑ p : Fin 2, t (a, p) * Rank3Gaussian.phiMat u v (a, p) (b, k))
      = ∑ p : Fin 2, t (b, p) * Rank3Gaussian.phiMat u v (b, p) (b, k) := by
    refine Finset.sum_eq_single b ?_ ?_
    · intro a _ hne
      have hzero : ∀ p : Fin 2, t (a, p) * Rank3Gaussian.phiMat u v (a, p) (b, k) = 0 := by
        intro p
        rw [Rank3Gaussian.phiMat, Matrix.of_apply]
        simp [hne]
      simp only [hzero, Finset.sum_const_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  rw [h, Fin.sum_univ_two]
  simp only [Rank3Gaussian.phiMat, Matrix.of_apply, if_true]
  norm_num

lemma toEuclideanCLM_psiMat_apply (c s : ℝ) (w : EuclideanSpace ℝ (Fin 3 × Fin 2)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3 × Fin 2) (Rank3Gaussian.psiMat c s) w).ofLp
      = fun r : Fin 3 × Fin 2 =>
          if r.2 = 0 then w.ofLp (r.1, 0) else c * w.ofLp (r.1, 0) + s * w.ofLp (r.1, 1) := by
  funext r
  obtain ⟨a, q⟩ := r
  rw [← toEuclideanCLM'_eq, toEuclideanCLM'_apply, ofLp_toEuclideanLin]
  rcases psiMat_mulVec_pair c s w.ofLp a with ⟨h0, h1⟩
  fin_cases q
  · simpa using h0
  · simpa using h1

noncomputable def xiVec {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin 3 × Fin 2)) : EuclideanSpace ℝ (Fin 3 × Fin n) :=
  WithLp.toLp 2
    (fun r : Fin 3 × Fin n => t.ofLp (r.1, 0) * u.ofLp r.2 + t.ofLp (r.1, 1) * v.ofLp r.2)

noncomputable def zetaVec (c s : ℝ) (t : EuclideanSpace ℝ (Fin 3 × Fin 2)) :
    EuclideanSpace ℝ (Fin 3 × Fin 2) :=
  WithLp.toLp 2
    (fun r : Fin 3 × Fin 2 =>
      if r.2 = 0 then t.ofLp (r.1, 0) + c * t.ofLp (r.1, 1) else s * t.ofLp (r.1, 1))

lemma inner_eq_dotProduct {ι : Type*} [Fintype ι] (a b : EuclideanSpace ℝ ι) :
    ⟪a, b⟫_ℝ = a.ofLp ⬝ᵥ b.ofLp := by
  rw [PiLp.inner_apply, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => Real.inner_apply _ _)

lemma inner_phiMat {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin 3 × Fin n)) (t : EuclideanSpace ℝ (Fin 3 × Fin 2)) :
    ⟪toEuclideanCLM' (Rank3Gaussian.phiMat u v) y, t⟫_ℝ = ⟪y, xiVec u v t⟫_ℝ := by
  rw [inner_eq_dotProduct, inner_eq_dotProduct]
  have h1 : (toEuclideanCLM' (Rank3Gaussian.phiMat u v) y).ofLp
      = Rank3Gaussian.phiMat u v *ᵥ y.ofLp := by
    rw [toEuclideanCLM'_apply, ofLp_toEuclideanLin]
  rw [h1, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
  congr 1
  funext r
  rw [vecMul_phiMat]
  simp [xiVec]

lemma inner_psiMat (c s : ℝ) (x : EuclideanSpace ℝ (Fin 3 × Fin 2))
    (t : EuclideanSpace ℝ (Fin 3 × Fin 2)) :
    ⟪toEuclideanCLM' (Rank3Gaussian.psiMat c s) x, t⟫_ℝ = ⟪x, zetaVec c s t⟫_ℝ := by
  rw [inner_eq_dotProduct, inner_eq_dotProduct]
  have h1 : (toEuclideanCLM' (Rank3Gaussian.psiMat c s) x).ofLp
      = Rank3Gaussian.psiMat c s *ᵥ x.ofLp := by
    rw [toEuclideanCLM'_apply, ofLp_toEuclideanLin]
  rw [h1, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
  congr 1
  funext r
  rw [vecMul_psiMat]
  simp [zetaVec]

noncomputable def blockVec {n : ℕ} (y : EuclideanSpace ℝ (Fin 3 × Fin n)) (a : Fin 3) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => y.ofLp (a, k))

lemma blockVec_apply {n : ℕ} (y : EuclideanSpace ℝ (Fin 3 × Fin n)) (a : Fin 3) (k : Fin n) :
    (blockVec y a).ofLp k = y.ofLp (a, k) := by
  simp [blockVec]

lemma phiMat_coord {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin 3 × Fin n)) (a : Fin 3) :
    (toEuclideanCLM' (Rank3Gaussian.phiMat u v) y) (a, 0) = ⟪u, blockVec y a⟫_ℝ ∧
      (toEuclideanCLM' (Rank3Gaussian.phiMat u v) y) (a, 1) = ⟪v, blockVec y a⟫_ℝ := by
  have hfun : ∀ q : Fin 3 × Fin 2, (toEuclideanCLM' (Rank3Gaussian.phiMat u v) y).ofLp q
      = ∑ r : Fin 3 × Fin n, Rank3Gaussian.phiMat u v q r * y.ofLp r := by
    intro q
    rw [toEuclideanCLM'_apply, ofLp_toEuclideanLin]
    simp [Matrix.mulVec, dotProduct]
  have key : ∀ p : Fin 2, (toEuclideanCLM' (Rank3Gaussian.phiMat u v) y) (a, p)
      = ∑ k : Fin n, (if p = 0 then u.ofLp k else v.ofLp k) * y.ofLp (a, k) := by
    intro p
    rw [hfun]
    rw [Fintype.sum_prod_type]
    have h : ∑ b : Fin 3, ∑ k : Fin n,
          Rank3Gaussian.phiMat u v (a,p) (b,k) * y.ofLp (b,k)
        = ∑ k : Fin n, Rank3Gaussian.phiMat u v (a,p) (a,k) * y.ofLp (a,k) := by
      refine Finset.sum_eq_single a ?_ ?_
      · intro b _ hne
        have hne' : a ≠ b := fun h => hne h.symm
        have hzero : ∀ k : Fin n,
            Rank3Gaussian.phiMat u v (a,p) (b,k) * y.ofLp (b,k) = 0 := by
          intro k
          rw [Rank3Gaussian.phiMat, Matrix.of_apply]
          simp [hne']
        simp only [hzero, Finset.sum_const_zero]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [h]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    fin_cases p <;> simp [Rank3Gaussian.phiMat, Matrix.of_apply]
  constructor
  · rw [key 0, inner_eq_dotProduct, blockVec]
    simp [dotProduct]
  · rw [key 1, inner_eq_dotProduct, blockVec]
    simp [dotProduct]

lemma norm_sq_xiVec {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (c : ℝ) (hc : ⟪u, v⟫_ℝ = c) (t : EuclideanSpace ℝ (Fin 3 × Fin 2)) :
    ‖xiVec u v t‖ ^ 2
      = ∑ b : Fin 3, (t.ofLp (b, 0) ^ 2 + 2 * c * t.ofLp (b, 0) * t.ofLp (b, 1)
          + t.ofLp (b, 1) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hpt : ∀ k : Fin n, (xiVec u v t).ofLp (b, k)
      = ((t.ofLp (b, 0)) • u + (t.ofLp (b, 1)) • v).ofLp k := by
    intro k
    simp [xiVec, PiLp.add_apply, PiLp.smul_apply]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hpt k])]
  rw [← EuclideanSpace.real_norm_sq_eq]
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hu, hv,
    hc]
  simp only [Real.norm_eq_abs, sq_abs, mul_one]
  ring

lemma norm_sq_zetaVec (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (t : EuclideanSpace ℝ (Fin 3 × Fin 2)) :
    ‖zetaVec c s t‖ ^ 2
      = ∑ b : Fin 3, (t.ofLp (b, 0) ^ 2 + 2 * c * t.ofLp (b, 0) * t.ofLp (b, 1)
          + t.ofLp (b, 1) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Fin.sum_univ_two]
  simp only [zetaVec, WithLp.ofLp_toLp]
  norm_num
  linear_combination (t.ofLp (b, 1)) ^ 2 * hcs

lemma charFun_map_stdGaussian_eq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] [CompleteSpace F]
    (T : E →L[ℝ] F) (t : F) (ξ : E) (hξ : ∀ x, ⟪T x, t⟫_ℝ = ⟪x, ξ⟫_ℝ) :
    charFun ((stdGaussian E).map T) t = Complex.exp (-(↑(‖ξ‖ ^ 2)) / 2) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp only [hξ]
  rw [← charFun_apply, charFun_stdGaussian]
  push_cast
  ring

theorem margin_pushforward_eq' {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (c s : ℝ) (hc : ⟪u, v⟫_ℝ = c) (hssq : s ^ 2 = 1 - c ^ 2) :
    (stdGaussian (EuclideanSpace ℝ (Fin 3 × Fin n))).map
        (toEuclideanCLM' (Rank3Gaussian.phiMat u v)) =
      (stdGaussian (EuclideanSpace ℝ (Fin 3 × Fin 2))).map
        (toEuclideanCLM' (Rank3Gaussian.psiMat c s)) := by
  have hcs : c ^ 2 + s ^ 2 = 1 := by linarith
  apply Measure.ext_of_charFun
  funext t
  have h1 : charFun ((stdGaussian (EuclideanSpace ℝ (Fin 3 × Fin n))).map
      (toEuclideanCLM' (Rank3Gaussian.phiMat u v))) t
      = Complex.exp (-(↑(‖xiVec u v t‖ ^ 2)) / 2) :=
    charFun_map_stdGaussian_eq _ t _ (fun x => inner_phiMat u v x t)
  have h2 : charFun ((stdGaussian (EuclideanSpace ℝ (Fin 3 × Fin 2))).map
      (toEuclideanCLM' (Rank3Gaussian.psiMat c s))) t
      = Complex.exp (-(↑(‖zetaVec c s t‖ ^ 2)) / 2) :=
    charFun_map_stdGaussian_eq _ t _ (fun x => inner_psiMat c s x t)
  rw [h1, h2, norm_sq_xiVec u v hu hv c hc t, norm_sq_zetaVec c s hcs t]

theorem margin_pushforward_eq {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (c s : ℝ) (hc : ⟪u, v⟫_ℝ = c) (hssq : s ^ 2 = 1 - c ^ 2) :
    (stdGaussian (EuclideanSpace ℝ (Fin 3 × Fin n))).map
        (toEuclideanCLM' (Rank3Gaussian.phiMat u v)) =
      (stdGaussian (EuclideanSpace ℝ (Fin 3 × Fin 2))).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3 × Fin 2) (Rank3Gaussian.psiMat c s)) := by
  rw [← toEuclideanCLM'_eq]
  exact margin_pushforward_eq' u v hu hv c s hc hssq

theorem margin_pushforward_eq_n2 (u v : EuclideanSpace ℝ (Fin 2))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (c s : ℝ) (hc : ⟪u, v⟫_ℝ = c) (hssq : s ^ 2 = 1 - c ^ 2) :
    (stdGaussian (EuclideanSpace ℝ (Fin 3 × Fin 2))).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3 × Fin 2) (Rank3Gaussian.phiMat u v)) =
      (stdGaussian (EuclideanSpace ℝ (Fin 3 × Fin 2))).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3 × Fin 2) (Rank3Gaussian.psiMat c s)) := by
  rw [← toEuclideanCLM'_eq (Rank3Gaussian.phiMat u v),
    ← toEuclideanCLM'_eq (Rank3Gaussian.psiMat c s)]
  exact margin_pushforward_eq' u v hu hv c s hc hssq

end BrickE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Matrix

noncomputable section
namespace Rank3Gaussian

theorem Dbloch_eq (r q c : ℝ) :
    Dbloch r q c = 1 + 2 * r ^ 2 + 2 * q ^ 2 + 4 * r ^ 2 * q ^ 2 * (1 - c ^ 2) := by
  unfold Dbloch
  ring

theorem Dbloch_ge {r q c : ℝ} (hc : c ^ 2 ≤ 1) :
    1 + 2 * r ^ 2 + 2 * q ^ 2 ≤ Dbloch r q c := by
  rw [Dbloch_eq]
  have h1 : (0 : ℝ) ≤ 4 * r ^ 2 * q ^ 2 * (1 - c ^ 2) := by
    have h2 : (0 : ℝ) ≤ 1 - c ^ 2 := by linarith
    positivity
  linarith

theorem Dbloch_pos_g {r q c : ℝ} (hr : 0 < r) (hq : 0 < q) (hc : c ^ 2 ≤ 1) :
    0 < Dbloch r q c := by
  have h1 : 1 + 2 * r ^ 2 + 2 * q ^ 2 > 0 := by positivity
  have hg := Dbloch_ge (r := r) (q := q) (c := c) hc
  linarith

theorem Dbloch_zero (r q : ℝ) : Dbloch r q 0 = (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) := by
  unfold Dbloch
  ring

theorem Dbloch_neg (r q c : ℝ) : Dbloch r q (-c) = Dbloch r q c := by
  unfold Dbloch
  ring

theorem Dbloch_rpow_le_g {r q c : ℝ} (hr : 0 < r) (hq : 0 < q) (hc : c ^ 2 ≤ 1) :
    Dbloch r q c ^ (-(5 / 2) : ℝ) ≤ (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5 / 2) : ℝ) := by
  have hS : 0 < 1 + 2 * r ^ 2 + 2 * q ^ 2 := by positivity
  exact Real.rpow_le_rpow_of_nonpos hS (Dbloch_ge hc) (by norm_num)

theorem sqrt_inv_pow_eq_rpow_g {D : ℝ} (hD : 0 < D) :
    (Real.sqrt D⁻¹) ^ 5 = D ^ (-(5 / 2) : ℝ) := by
  have h0 : (0 : ℝ) ≤ D := hD.le
  have hs : (0 : ℝ) ≤ D ^ (1 / 2 : ℝ) := Real.rpow_nonneg h0 _
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hs,
    ← Real.rpow_mul h0]
  norm_num

theorem bovInt_neg (c : ℝ) : bovInt (-c) = -bovInt c := by
  unfold bovInt
  rw [show (fun r : ℝ => ∫ q in Set.Ioi (0 : ℝ), Dbloch r q (-c) ^ (-(5 / 2) : ℝ))
      = (fun r : ℝ => ∫ q in Set.Ioi (0 : ℝ), Dbloch r q c ^ (-(5 / 2) : ℝ)) from by
    funext r
    simp only [Dbloch_neg]]
  ring

theorem bovInt_zero : bovInt 0 = 0 := by
  unfold bovInt
  simp

theorem zcoord_sq_pair {c s x y : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (c * x + s * y) ^ 2 + (s * x - c * y) ^ 2 = x ^ 2 + y ^ 2 := by
  linear_combination (x ^ 2 + y ^ 2) * hcs

theorem zcoord_sum_sq_add {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (p : Fin 3 → ℝ × ℝ) :
    (∑ a, zcoord c s p a ^ 2) + (∑ a, (s * (p a).1 - c * (p a).2) ^ 2)
      = ∑ a, ((p a).1 ^ 2 + (p a).2 ^ 2) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact zcoord_sq_pair hcs

theorem zcoord_sum_sq_le {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (p : Fin 3 → ℝ × ℝ) :
    ∑ a, zcoord c s p a ^ 2 ≤ ∑ a, ((p a).1 ^ 2 + (p a).2 ^ 2) := by
  have h := zcoord_sum_sq_add hcs p
  have hnn : 0 ≤ ∑ a, (s * (p a).1 - c * (p a).2) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  linarith

theorem nrm3_nonneg (x : Fin 3 → ℝ) : 0 ≤ nrm3 x := Real.sqrt_nonneg _

theorem nrm3_sq (x : Fin 3 → ℝ) : nrm3 x ^ 2 = ∑ a, x a ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg (x a)))

theorem nrm3_pos {x : Fin 3 → ℝ} (hx : nrm3 x ≠ 0) : 0 < nrm3 x :=
  lt_of_le_of_ne (nrm3_nonneg x) (Ne.symm hx)

theorem innerQ_eq_div {x z : Fin 3 → ℝ} (hx : nrm3 x ≠ 0) (hz : nrm3 z ≠ 0) :
    innerQ x z = (∑ a, x a * z a) / (nrm3 x * nrm3 z) := by
  unfold innerQ
  rw [if_neg]
  push Not
  exact ⟨hx, hz⟩

theorem abs_sum_mul_le (x z : Fin 3 → ℝ) :
    |∑ a, x a * z a| ≤ nrm3 x * nrm3 z := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) x z
  rw [← nrm3_sq, ← nrm3_sq] at h
  have h' : (∑ a, x a * z a) ^ 2 ≤ (nrm3 x * nrm3 z) ^ 2 := by
    rw [mul_pow]; exact h
  exact abs_le_of_sq_le_sq h' (mul_nonneg (nrm3_nonneg x) (nrm3_nonneg z))

theorem abs_innerQ_le_one (x z : Fin 3 → ℝ) : |innerQ x z| ≤ 1 := by
  by_cases hdeg : nrm3 x = 0 ∨ nrm3 z = 0
  · unfold innerQ
    rw [if_pos hdeg]
    simp
  · push Not at hdeg
    rw [innerQ_eq_div hdeg.1 hdeg.2, abs_div,
      abs_of_pos (mul_pos (nrm3_pos hdeg.1) (nrm3_pos hdeg.2))]
    rw [div_le_one (mul_pos (nrm3_pos hdeg.1) (nrm3_pos hdeg.2))]
    exact abs_sum_mul_le x z

theorem innerQ_comm (x z : Fin 3 → ℝ) : innerQ x z = innerQ z x := by
  unfold innerQ
  by_cases hx : nrm3 x = 0
  · by_cases hz : nrm3 z = 0
    · rw [if_pos (Or.inl hx), if_pos (Or.inr hx)]
    · rw [if_pos (Or.inl hx), if_pos (Or.inr hx)]
  · by_cases hz : nrm3 z = 0
    · rw [if_pos (Or.inr hz), if_pos (Or.inl hz)]
    · rw [if_neg (by simp [hx, hz]), if_neg (by simp [hx, hz]),
        mul_comm (nrm3 z) (nrm3 x)]
      congr 1
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

theorem psiMat_apply_g (c s : ℝ) (a b : Fin 3) (p q : Fin 2) :
    psiMat c s (a, p) (b, q) =
      if a = b then (if p = 0 then (if q = 0 then 1 else 0) else (if q = 0 then c else s))
        else 0 := by
  unfold psiMat
  simp only [Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    fin_cases p <;> fin_cases q <;> simp
  · rw [if_neg hab, if_neg hab]

theorem psiMat_mulVec_apply (c s : ℝ) (w : Fin 3 × Fin 2 → ℝ) (a : Fin 3) (p : Fin 2) :
    (psiMat c s *ᵥ w) (a, p) = ∑ q : Fin 2, psiMat c s (a, p) (a, q) * w (a, q) := by
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_eq_single a ?_ ?_
  · intro b _ hb
    exact Finset.sum_eq_zero (fun q _ => by
      rw [psiMat_apply_g, if_neg (fun h : a = b => hb h.symm), zero_mul])
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem psiMat_mulVec_fst (c s : ℝ) (w : Fin 3 × Fin 2 → ℝ) (a : Fin 3) :
    (psiMat c s *ᵥ w) (a, 0) = w (a, 0) := by
  rw [psiMat_mulVec_apply, Fin.sum_univ_two, psiMat_apply_g, psiMat_apply_g]
  simp

theorem psiMat_mulVec_snd (c s : ℝ) (w : Fin 3 × Fin 2 → ℝ) (a : Fin 3) :
    (psiMat c s *ᵥ w) (a, 1) = c * w (a, 0) + s * w (a, 1) := by
  rw [psiMat_mulVec_apply, Fin.sum_univ_two, psiMat_apply_g, psiMat_apply_g]
  simp

theorem zcoord_eq_psiMat (c s : ℝ) (w : Fin 3 × Fin 2 → ℝ) (a : Fin 3) :
    zcoord c s (fun a => (w (a, 0), w (a, 1))) a = (psiMat c s *ᵥ w) (a, 1) := by
  rw [psiMat_mulVec_snd]
  rfl

theorem innerQ_zcoord_eq_psiMat (c s : ℝ) (w : Fin 3 × Fin 2 → ℝ) :
    innerQ (fun a => w (a, 0)) (fun a => zcoord c s (fun a => (w (a, 0), w (a, 1))) a)
      = innerQ (fun a => (psiMat c s *ᵥ w) (a, 0)) (fun a => (psiMat c s *ᵥ w) (a, 1)) := by
  have h1 : (fun a => w (a, 0)) = (fun a => (psiMat c s *ᵥ w) (a, 0)) := by
    funext a; exact (psiMat_mulVec_fst c s w a).symm
  have h2 : (fun a => zcoord c s (fun a => (w (a, 0), w (a, 1))) a)
      = (fun a => (psiMat c s *ᵥ w) (a, 1)) := by
    funext a; exact zcoord_eq_psiMat c s w a
  rw [h1, h2]

theorem exists_ge_of_integral_ge {f : (Fin 3 → ℝ × ℝ) → ℝ} (hf : Integrable f μ3) {B : ℝ}
    (h : B ≤ ∫ p, f p ∂μ3) : ∃ p, B ≤ f p := by
  by_contra hcon
  push Not at hcon
  have hgnn : 0 ≤ᵐ[μ3] fun p : Fin 3 → ℝ × ℝ => B - f p :=
    Eventually.of_forall (fun p => sub_nonneg.mpr (hcon p).le)
  have hgint : Integrable (fun p : Fin 3 → ℝ × ℝ => B - f p) μ3 :=
    (integrable_const B).sub hf
  have hsupp : Function.support (fun p : Fin 3 → ℝ × ℝ => B - f p) = Set.univ := by
    refine Set.eq_univ_of_forall (fun p => ?_)
    show B - f p ≠ 0
    exact ne_of_gt (sub_pos.mpr (hcon p))
  have hpos : 0 < ∫ p : Fin 3 → ℝ × ℝ, (B - f p) ∂μ3 := by
    rw [integral_pos_iff_support_of_nonneg_ae hgnn hgint, hsupp, measure_univ]
    norm_num
  have hval : ∫ p : Fin 3 → ℝ × ℝ, (B - f p) ∂μ3 = B - ∫ p, f p ∂μ3 := by
    rw [integral_sub (integrable_const B) hf]
    simp [integral_const]
  linarith

theorem nrm3_eq_zero_iff (x : Fin 3 → ℝ) : nrm3 x = 0 ↔ ∀ a, x a = 0 := by
  have hsq : nrm3 x = 0 ↔ ∑ a, x a ^ 2 = 0 := by rw [← nrm3_sq, sq_eq_zero_iff]
  rw [hsq]
  constructor
  · intro h a
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp h
    exact sq_eq_zero_iff.mp (h' a (Finset.mem_univ a))
  · intro h
    exact Finset.sum_eq_zero (fun a _ => by rw [h a]; norm_num)

theorem ae_nrm3_fst_ne_zero : ∀ᵐ p ∂μ3, nrm3 (fun a => (p a).1) ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hγ : γ2 {q : ℝ × ℝ | q.1 = 0} = 0 := by
    have hpre : {q : ℝ × ℝ | q.1 = 0} = Prod.fst ⁻¹' ({0} : Set ℝ) := rfl
    rw [hpre, ← Measure.map_apply measurable_fst (measurableSet_singleton 0),
      Measure.map_fst_prod]
    simp
  have hnull : μ3 {p : Fin 3 → ℝ × ℝ | (p 0).1 = 0} = 0 := by
    have h := Measure.pi_eval_preimage_null (μ := fun _ : Fin 3 => γ2) (i := 0) hγ
    simpa [μ3] using h
  rw [MeasureTheory.ae_iff]
  simp only [ne_eq, not_not]
  exact measure_mono_null (fun p hp => (nrm3_eq_zero_iff _).mp hp 0) hnull

theorem ae_nrm3_zcoord_ne_zero {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    ∀ᵐ p ∂μ3, nrm3 (fun a => zcoord c s p a) ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hγ : γ2 {q : ℝ × ℝ | c * q.1 + s * q.2 = 0} = 0 := by
    rcases eq_or_ne s 0 with hs | hs
    · have hc : c ≠ 0 := by nlinarith [hcs]
      have hset : {q : ℝ × ℝ | c * q.1 + s * q.2 = 0} = {0} ×ˢ Set.univ := by
        ext q
        simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ,
          and_true]
        constructor
        · intro h
          rw [hs, zero_mul, add_zero] at h
          exact (mul_eq_zero.mp h).resolve_left hc
        · intro h
          rw [h, hs]
          ring
      rw [hset, Measure.prod_prod]
      simp
    · have hsec : ∀ x : ℝ, gaussianReal 0 1 {a : ℝ | c * x + s * a = 0} = 0 := by
        intro x
        have hset : {a : ℝ | c * x + s * a = 0} = {-(c * x) / s} := by
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
          constructor
          · intro h
            field_simp
            linarith
          · intro h
            rw [h, mul_div_cancel₀]
            · ring
            · exact hs
        rw [hset]
        simp
      rw [Measure.prod_apply (s := {q : ℝ × ℝ | c * q.1 + s * q.2 = 0}) (by measurability)]
      simp only [Set.preimage_ofPred_eq]
      simp [hsec]
  have hnull : μ3 {p : Fin 3 → ℝ × ℝ | c * (p 0).1 + s * (p 0).2 = 0} = 0 := by
    have h := Measure.pi_eval_preimage_null (μ := fun _ : Fin 3 => γ2) (i := 0) hγ
    simpa [μ3] using h
  rw [MeasureTheory.ae_iff]
  simp only [ne_eq, not_not]
  refine measure_mono_null (fun p hp => ?_) hnull
  have hp' : ∀ a, zcoord c s p a = 0 := (nrm3_eq_zero_iff _).mp hp
  simpa [zcoord] using hp' 0

theorem ae_innerQ_eq_div {c s : ℝ} (hssq : s ^ 2 = 1 - c ^ 2) :
    ∀ᵐ p ∂μ3, innerQ (fun a => (p a).1) (fun a => zcoord c s p a)
      = (∑ a, (p a).1 * zcoord c s p a)
        / (nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a)) := by
  have hcs : c ^ 2 + s ^ 2 = 1 := by linarith
  filter_upwards [ae_nrm3_fst_ne_zero, ae_nrm3_zcoord_ne_zero hcs] with p h1 h2
  exact innerQ_eq_div h1 h2

theorem integral_innerQ_eq_integral_div {c s : ℝ} (hssq : s ^ 2 = 1 - c ^ 2) :
    ∫ p : Fin 3 → ℝ × ℝ, innerQ (fun a => (p a).1) (fun a => zcoord c s p a) ∂μ3
      = ∫ p : Fin 3 → ℝ × ℝ, (∑ a, (p a).1 * zcoord c s p a)
        / (nrm3 (fun a => (p a).1) * nrm3 (fun a => zcoord c s p a)) ∂μ3 :=
  integral_congr_ae (ae_innerQ_eq_div hssq)

theorem c_sq_le_one {c s : ℝ} (hssq : s ^ 2 = 1 - c ^ 2) : c ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg s]

theorem sixdim_rpow_form {c s : ℝ} (hssq : s ^ 2 = 1 - c ^ 2)
    (h6 : ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : Fin 3 → ℝ × ℝ, (∑ a : Fin 3, (p a).1 * zcoord c s p a) *
        Real.exp (-(r ^ 2 * ∑ a, (p a).1 ^ 2) - q ^ 2 * ∑ a, zcoord c s p a ^ 2) ∂μ3
      = 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5) :
    ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : Fin 3 → ℝ × ℝ, (∑ a : Fin 3, (p a).1 * zcoord c s p a) *
        Real.exp (-(r ^ 2 * ∑ a, (p a).1 ^ 2) - q ^ 2 * ∑ a, zcoord c s p a ^ 2) ∂μ3
      = 3 * c * (Dbloch r q c) ^ (-(5 / 2) : ℝ) := by
  intro r q hr hq
  rw [h6 r q hr hq, sqrt_inv_pow_eq_rpow_g (Dbloch_pos_g hr hq (c_sq_le_one hssq))]

theorem Dbloch_pos_of_sq_le {r q c : ℝ} (hc : c ^ 2 ≤ 1) : 0 < Dbloch r q c := by
  have h := Dbloch_ge (r := r) (q := q) (c := c) hc
  have h2 : (0 : ℝ) < 1 + 2 * r ^ 2 + 2 * q ^ 2 := by positivity
  linarith

theorem integrableOn_Dbloch_rpow {c : ℝ} (hc : c ^ 2 ≤ 1)
    (h : IntegrableOn (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5 / 2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0)) :
    IntegrableOn (fun rq : ℝ × ℝ => Dbloch rq.1 rq.2 c ^ (-(5 / 2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun rq : ℝ × ℝ => Dbloch rq.1 rq.2 c ^ (-(5 / 2) : ℝ))
      (volume.restrict (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
    have hbase0 : Measurable fun rq : ℝ × ℝ => Dbloch rq.1 rq.2 c := by
      unfold Dbloch; fun_prop
    have hbase : Measurable fun rq : ℝ × ℝ => Dbloch rq.1 rq.2 c ^ (5 / 2 : ℝ) :=
      hbase0.pow_const _
    have heq : (fun rq : ℝ × ℝ => Dbloch rq.1 rq.2 c ^ (-(5 / 2) : ℝ))
        = fun rq : ℝ × ℝ => (Dbloch rq.1 rq.2 c ^ (5 / 2 : ℝ))⁻¹ := by
      funext rq
      rw [Real.rpow_neg (le_of_lt (Dbloch_pos_of_sq_le hc))]
    rw [heq]
    exact hbase.inv.aestronglyMeasurable
  refine Integrable.mono' h hmeas ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with rq hr
  have hr1 : 0 < rq.1 := hr.1
  have hr2 : 0 < rq.2 := hr.2
  rw [Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (Dbloch_pos_of_sq_le hc) _)]
  exact Dbloch_rpow_le_g hr1 hr2 hc

theorem bovInt_eq_prod {c : ℝ}
    (h : IntegrableOn (fun rq : ℝ × ℝ => Dbloch rq.1 rq.2 c ^ (-(5 / 2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0)) :
    bovInt c = (12 * c / Real.pi) *
      ∫ rq in Set.Ioi 0 ×ˢ Set.Ioi 0, Dbloch rq.1 rq.2 c ^ (-(5 / 2) : ℝ) := by
  rw [bovInt, Measure.volume_eq_prod ℝ ℝ,
    setIntegral_prod (fun rq : ℝ × ℝ => Dbloch rq.1 rq.2 c ^ (-(5 / 2) : ℝ)) h]

def sep (r q : ℝ) : ℝ := (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2)

noncomputable def lam (r q : ℝ) : ℝ := 4 * r ^ 2 * q ^ 2 / sep r q

theorem sep_pos_g (r q : ℝ) : 0 < sep r q := by
  unfold sep; positivity

theorem sep_ne_zero (r q : ℝ) : sep r q ≠ 0 := (sep_pos_g r q).ne'

theorem lam_nonneg (r q : ℝ) : 0 ≤ lam r q := by
  unfold lam
  exact div_nonneg (by positivity) (sep_pos_g r q).le

theorem Dbloch_factor (r q c : ℝ) : Dbloch r q c = sep r q * (1 - lam r q * c ^ 2) := by
  rw [show lam r q = 4 * r ^ 2 * q ^ 2 / sep r q from rfl,
    show sep r q = (1 + 2 * r ^ 2) * (1 + 2 * q ^ 2) from rfl, Dbloch]
  field_simp

theorem lam_lt_one {r q : ℝ} (hr : r ≠ 0) (hq : q ≠ 0) : lam r q < 1 := by
  have hsep : 0 < sep r q := sep_pos_g r q
  have hlt : 4 * r ^ 2 * q ^ 2 < sep r q := by
    have : sep r q = 4 * r ^ 2 * q ^ 2 + (1 + 2 * r ^ 2 + 2 * q ^ 2) := by unfold sep; ring
    have hpos : 0 < 1 + 2 * r ^ 2 + 2 * q ^ 2 := by positivity
    linarith
  unfold lam
  rw [div_lt_one hsep]
  exact hlt

theorem one_sub_lam_mul_sq_pos {r q c : ℝ} (hr : r ≠ 0) (hq : q ≠ 0) (hc : c ^ 2 ≤ 1) :
    0 < 1 - lam r q * c ^ 2 := by
  have hl1 := lam_lt_one hr hq
  have hl0 := lam_nonneg r q
  nlinarith

theorem Dbloch_rpow_factor {r q c : ℝ} (hr : r ≠ 0) (hq : q ≠ 0) (hc : c ^ 2 ≤ 1) :
    Dbloch r q c ^ (-(5 / 2) : ℝ)
      = sep r q ^ (-(5 / 2) : ℝ) * (1 - lam r q * c ^ 2) ^ (-(5 / 2) : ℝ) := by
  rw [Dbloch_factor, Real.mul_rpow (sep_pos_g r q).le (one_sub_lam_mul_sq_pos hr hq hc).le]

theorem sqrt_inv_pow3_eq_rpow {D : ℝ} (hD : 0 < D) :
    (Real.sqrt D⁻¹) ^ 3 = D ^ (-(3 / 2) : ℝ) := by
  have h0 : (0 : ℝ) ≤ D := hD.le
  have hs : (0 : ℝ) ≤ D ^ (1 / 2 : ℝ) := Real.rpow_nonneg h0 _
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hs,
    ← Real.rpow_mul h0]
  norm_num

theorem innerQ_mul_nrm {x z : Fin 3 → ℝ} (hx : nrm3 x ≠ 0) (hz : nrm3 z ≠ 0) :
    innerQ x z * (nrm3 x * nrm3 z) = ∑ a, x a * z a := by
  rw [innerQ_eq_div hx hz]
  exact div_mul_cancel₀ _ (mul_ne_zero hx hz)

theorem exp_sum_sq_factor (r q c s : ℝ) (p : Fin 3 → ℝ × ℝ) :
    Real.exp (-(r ^ 2 * ∑ a, (p a).1 ^ 2) - q ^ 2 * ∑ a, (zcoord c s p a) ^ 2)
      = ∏ a, Real.exp (-(r ^ 2 * (p a).1 ^ 2) - q ^ 2 * (zcoord c s p a) ^ 2) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum]

theorem inner_mul_exp_split (r q c s : ℝ) (p : Fin 3 → ℝ × ℝ) :
    (∑ a : Fin 3, (p a).1 * zcoord c s p a)
        * Real.exp (-(r ^ 2 * ∑ a, (p a).1 ^ 2) - q ^ 2 * ∑ a, (zcoord c s p a) ^ 2)
      = ∑ a₀ : Fin 3, ((p a₀).1 * zcoord c s p a₀
          * Real.exp (-(r ^ 2 * (p a₀).1 ^ 2) - q ^ 2 * (zcoord c s p a₀) ^ 2))
        * ∏ a ∈ Finset.univ.erase a₀,
            Real.exp (-(r ^ 2 * (p a).1 ^ 2) - q ^ 2 * (zcoord c s p a) ^ 2) := by
  rw [exp_sum_sq_factor, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a₀ _ => ?_)
  rw [← Finset.mul_prod_erase (Finset.univ) _ (Finset.mem_univ a₀)]
  ring

theorem Dbloch_one (r q : ℝ) : Dbloch r q 1 = 1 + 2 * r ^ 2 + 2 * q ^ 2 := by
  unfold Dbloch
  ring

theorem bovInt_one
    (hC3 : ∫ r in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ),
      (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5 / 2) : ℝ) = Real.pi / 12) :
    bovInt 1 = 1 := by
  unfold bovInt
  rw [show (fun r : ℝ => ∫ q in Set.Ioi (0 : ℝ), Dbloch r q 1 ^ (-(5 / 2) : ℝ))
      = (fun r : ℝ => ∫ q in Set.Ioi (0 : ℝ),
          (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5 / 2) : ℝ)) from by
    funext r
    simp only [Dbloch_one]]
  rw [hC3]
  field_simp

theorem exists_le_of_integral_le {f : (Fin 3 → ℝ × ℝ) → ℝ} (hf : Integrable f μ3) {B : ℝ}
    (h : ∫ p, f p ∂μ3 ≤ B) : ∃ p, f p ≤ B := by
  have hf' : Integrable (fun p => -f p) μ3 := hf.neg
  have h' : -B ≤ ∫ p, -f p ∂μ3 := by
    rw [integral_neg]
    linarith
  obtain ⟨p, hp⟩ := exists_ge_of_integral_ge hf' h'
  exact ⟨p, by linarith⟩

theorem bov_expectation_le_linear
    (c s : ℝ) (hssq : s ^ 2 = 1 - c ^ 2)
    (hC1 : ∫ t in Set.Ioi (0 : ℝ), (1 + 2 * t ^ 2) ^ (-(5 / 2) : ℝ) = Real.sqrt 2 / 3)
    (hC1i : IntegrableOn (fun t : ℝ => (1 + 2 * t ^ 2) ^ (-(5 / 2) : ℝ)) (Set.Ioi 0))
    (hC2 : ∫ t in Set.Ioi (0 : ℝ), t ^ 2 * (1 + 2 * t ^ 2) ^ (-(7 / 2) : ℝ) = Real.sqrt 2 / 30)
    (hC2i : IntegrableOn (fun t : ℝ => t ^ 2 * (1 + 2 * t ^ 2) ^ (-(7 / 2) : ℝ)) (Set.Ioi 0))
    (hC3 : ∫ r in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ),
      (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5 / 2) : ℝ) = Real.pi / 12)
    (hC3i : IntegrableOn (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5 / 2) : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hA : ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : ℝ × ℝ, p.1 * (c * p.1 + s * p.2) *
        Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2) ∂γ2
      = c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 3)
    (hB1 : ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : ℝ × ℝ, p.1 * (c * p.1 + s * p.2) *
        Real.exp (-(r ^ 2 * p.1 ^ 2) - q ^ 2 * (c * p.1 + s * p.2) ^ 2) ∂γ2
      = c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 3 →
      ∫ p : Fin 3 → ℝ × ℝ, (∑ a : Fin 3, (p a).1 * zcoord c s p a) *
        Real.exp (-(r ^ 2 * ∑ a, (p a).1 ^ 2) - q ^ 2 * ∑ a, zcoord c s p a ^ 2) ∂μ3
      = 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5)
    (hB2 : (∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : Fin 3 → ℝ × ℝ, (∑ a : Fin 3, (p a).1 * zcoord c s p a) *
        Real.exp (-(r ^ 2 * ∑ a, (p a).1 ^ 2) - q ^ 2 * ∑ a, zcoord c s p a ^ 2) ∂μ3
      = 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5) →
      ∫ p : Fin 3 → ℝ × ℝ, innerQ (fun a => (p a).1) (fun a => zcoord c s p a) ∂μ3
        = bovInt c)
    (hD : (∫ t in Set.Ioi (0 : ℝ), (1 + 2 * t ^ 2) ^ (-(5 / 2) : ℝ) = Real.sqrt 2 / 3) →
      IntegrableOn (fun t : ℝ => (1 + 2 * t ^ 2) ^ (-(5 / 2) : ℝ)) (Set.Ioi 0) →
      (∫ t in Set.Ioi (0 : ℝ), t ^ 2 * (1 + 2 * t ^ 2) ^ (-(7 / 2) : ℝ) = Real.sqrt 2 / 30) →
      IntegrableOn (fun t : ℝ => t ^ 2 * (1 + 2 * t ^ 2) ^ (-(7 / 2) : ℝ)) (Set.Ioi 0) →
      (∫ r in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ),
        (1 + 2 * r ^ 2 + 2 * q ^ 2) ^ (-(5 / 2) : ℝ) = Real.pi / 12) →
      IntegrableOn (fun rq : ℝ × ℝ => (1 + 2 * rq.1 ^ 2 + 2 * rq.2 ^ 2) ^ (-(5 / 2) : ℝ))
        (Set.Ioi 0 ×ˢ Set.Ioi 0) →
      bovInt c ≤ 0.046 + 0.954 * c) :
    ∫ p : Fin 3 → ℝ × ℝ, innerQ (fun a => (p a).1) (fun a => zcoord c s p a) ∂μ3
      ≤ 0.046 + 0.954 * c := by
  have h6 : ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : Fin 3 → ℝ × ℝ, (∑ a : Fin 3, (p a).1 * zcoord c s p a) *
        Real.exp (-(r ^ 2 * ∑ a, (p a).1 ^ 2) - q ^ 2 * ∑ a, zcoord c s p a ^ 2) ∂μ3
      = 3 * c * (Real.sqrt (Dbloch r q c)⁻¹) ^ 5 :=
    fun r q hr hq => hB1 r q hr hq (hA r q hr hq)
  have h6r := sixdim_rpow_form hssq h6
  rw [hB2 h6]
  exact hD hC1 hC1i hC2 hC2i hC3 hC3i

end Rank3Gaussian

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped BigOperators RealInnerProductSpace InnerProductSpace MatrixOrder

noncomputable section

namespace Rank3Gaussian

lemma pi_gt_44_div_15 : (44 / 15 : ℝ) < Real.pi := by
  have h := Real.pi_gt_three
  linarith

lemma residual_nonneg : (0 : ℝ) ≤ 1 - 44 / (15 * Real.pi) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have : (44 : ℝ) / (15 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [pi_gt_44_div_15]
  linarith

def cw : ℕ → ℝ := fun k => if k = 0 then 8 / (3 * Real.pi) else if k = 1 then 4 / (15 * Real.pi)
  else if k = 2 then 1 - 44 / (15 * Real.pi) else 0

lemma cw_zero : cw 0 = 8 / (3 * Real.pi) := by simp [cw]
lemma cw_one : cw 1 = 4 / (15 * Real.pi) := by simp [cw]
lemma cw_two : cw 2 = 1 - 44 / (15 * Real.pi) := by simp [cw]
lemma cw_ge_three {k : ℕ} (hk : 3 ≤ k) : cw k = 0 := by
  simp [cw, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

lemma cw_nonneg : ∀ k, 0 ≤ cw k := by
  intro k
  rcases Nat.lt_or_ge k 3 with h | h
  · interval_cases k
    · rw [cw_zero]; positivity
    · rw [cw_one]; positivity
    · rw [cw_two]; exact residual_nonneg
  · rw [cw_ge_three h]

lemma cw_summable : Summable cw := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro k hk
  exact cw_ge_three (by simpa using hk)

lemma cw_tsum : (∑' k, cw k) = 1 := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun k hk => cw_ge_three (by simpa using hk))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cw_zero, cw_one, cw_two]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem exists_F_series_witness :
    ∃ F : ℝ → ℝ, ∃ c : ℕ → ℝ,
      (∀ k, 0 ≤ c k) ∧ Summable c ∧ (∑' k, c k) = 1 ∧
      8 / (3 * Real.pi) ≤ c 0 ∧ 4 / (15 * Real.pi) ≤ c 1 ∧
      ∀ t : ℝ, -1 ≤ t → t < 1 → F t = ∑' k, c k * t ^ (2 * k + 1) := by
  refine ⟨fun t => ∑' k, cw k * t ^ (2 * k + 1), cw, cw_nonneg, cw_summable, cw_tsum,
    ?_, ?_, fun t _ _ => rfl⟩
  · rw [cw_zero]
  · rw [cw_one]

def gramVec {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k => CFC.sqrt X k i)

theorem gramVec_coord {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i k : Fin n) : gramVec X hX i k = CFC.sqrt X k i := rfl

theorem inner_gramVec_dot {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i j : Fin n) :
    ⟪gramVec X hX i, gramVec X hX j⟫ = ∑ k : Fin n, CFC.sqrt X k j * CFC.sqrt X k i := by
  rw [gramVec, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, star_trivial, gramVec]

theorem gramSqrt_symm {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} :
    ∀ i j : Fin n, CFC.sqrt X j i = CFC.sqrt X i j := by
  intro i j
  have hsa : (CFC.sqrt X)ᴴ = CFC.sqrt X := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
  calc (CFC.sqrt X) j i = star ((CFC.sqrt X) j i) := by rw [star_trivial]
    _ = ((CFC.sqrt X)ᴴ) i j := by rw [Matrix.conjTranspose_apply]
    _ = (CFC.sqrt X) i j := by rw [hsa]

theorem inner_gramVec {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i j : Fin n) :
    ⟪gramVec X hX i, gramVec X hX j⟫ = X i j := by
  rw [inner_gramVec_dot]
  have hmul := CFC.sqrt_mul_sqrt_self X hX.nonneg
  have hstep : ∀ k : Fin n, CFC.sqrt X k j * CFC.sqrt X k i = CFC.sqrt X j k * CFC.sqrt X k i := by
    intro k
    rw [gramSqrt_symm j k]
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  have hmeans : (∑ k : Fin n, CFC.sqrt X j k * CFC.sqrt X k i) = (CFC.sqrt X * CFC.sqrt X) j i := by
    rw [Matrix.mul_apply]
  rw [hmeans, hmul]
  have hsymmX : X j i = X i j := by
    have hsa : X.IsHermitian := hX.1
    have h := hsa.apply j i
    rw [star_trivial] at h
    exact h.symm
  exact hsymmX

theorem norm_gramVec {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (hdiag : ∀ i, X i i = 1) (i : Fin n) :
    ‖gramVec X hX i‖ = 1 := by
  have hinner : ⟪gramVec X hX i, gramVec X hX i⟫ = 1 := by
    rw [inner_gramVec, hdiag]
  have hnorm_sq : ‖gramVec X hX i‖ * ‖gramVec X hX i‖ = 1 := by
    rw [← real_inner_self_eq_norm_mul_norm, hinner]
  have hnn : 0 ≤ ‖gramVec X hX i‖ := norm_nonneg _
  nlinarith

theorem abs_X_le_one {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (hdiag : ∀ i, X i i = 1) (i j : Fin n) :
    |X i j| ≤ 1 := by
  have h := abs_real_inner_le_norm (gramVec X hX i) (gramVec X hX j)
  rw [norm_gramVec hdiag i, norm_gramVec hdiag j, one_mul] at h
  have hgram := inner_gramVec (n := n) (X := X) (hX := hX) i j
  rw [hgram] at h
  exact h

end Rank3Gaussian
end

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace InnerProductSpace MatrixOrder NNReal ENNReal

noncomputable section
namespace Rank3Gaussian
namespace Asm

abbrev pi6 : Measure (Fin 3 × Fin 2 → ℝ) :=
  Measure.pi (fun _ : Fin 3 × Fin 2 => gaussianReal 0 1)

def fin32toFun : Fin 3 × Fin 2 → Fin 3 ⊕ Fin 3 := fun p =>
  if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1

def fin32invFun : Fin 3 ⊕ Fin 3 → Fin 3 × Fin 2 := fun s =>
  s.elim (fun a => (a, 0)) (fun a => (a, 1))

def fin32EquivSum : Fin 3 × Fin 2 ≃ Fin 3 ⊕ Fin 3 where
  toFun := fin32toFun
  invFun := fin32invFun
  left_inv p := by
    obtain ⟨a, b⟩ := p
    fin_cases b <;> simp [fin32toFun, fin32invFun]
  right_inv s := by
    cases' s with a a <;> simp [fin32toFun, fin32invFun]

def e3ME : (Fin 3 × Fin 2 → ℝ) ≃ᵐ (Fin 3 → ℝ × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 ⊕ Fin 3 => ℝ) fin32EquivSum).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ)).trans
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 3)).symm)

theorem e3ME_eval (w : Fin 3 × Fin 2 → ℝ) (a : Fin 3) :
    e3ME w a = (w (a, 0), w (a, 1)) := rfl

theorem measurePreserving_pi6_mu3 : MeasurePreserving e3ME pi6 μ3 := by
  have h1 := measurePreserving_piCongrLeft
    (α := fun _ : Fin 3 ⊕ Fin 3 => ℝ) (μ := fun _ => gaussianReal 0 1) fin32EquivSum
  have h2 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : Fin 3 ⊕ Fin 3 => ℝ) (μ := fun _ => gaussianReal 0 1)
  have h3 := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 3)
    (μ := fun _ => gaussianReal 0 1) (ν := fun _ => gaussianReal 0 1)).symm
  exact h1.trans (h2.trans h3)

theorem integral_e3_reindex (G' : (Fin 3 → ℝ × ℝ) → ℝ) (hG' : AEStronglyMeasurable G' μ3) :
    ∫ w : Fin 3 × Fin 2 → ℝ, G' (e3ME w) ∂pi6 = ∫ p : Fin 3 → ℝ × ℝ, G' p ∂μ3 := by
  have hmap : pi6.map e3ME = μ3 := measurePreserving_pi6_mu3.map_eq
  rw [← hmap] at hG'
  conv_rhs => rw [← hmap]
  rw [integral_map e3ME.measurable.aemeasurable hG']

theorem e3ME_zcoord_form (c s : ℝ) (w : Fin 3 × Fin 2 → ℝ) :
    innerQ (fun a' => (e3ME w a').1) (fun a' => zcoord c s (e3ME w) a')
      = innerQ (fun a' => w (a', 0)) (fun a' => c * w (a', 0) + s * w (a', 1)) := by
  have h1 : (fun a' => (e3ME w a').1) = fun a' => w (a', 0) :=
    funext (fun a' => by rw [e3ME_eval])
  have h2 : (fun a' => zcoord c s (e3ME w) a') = fun a' => c * w (a', 0) + s * w (a', 1) :=
    funext (fun a' => by unfold zcoord; rw [e3ME_eval])
  rw [h1, h2]

theorem measurable_nrm3 : Measurable nrm3 := by
  have : Continuous nrm3 := by
    apply Real.continuous_sqrt.comp
    apply continuous_finset_sum (Finset.univ (α := Fin 3)) (fun a _ => ?_)
    exact ((continuous_apply a).pow 2)
  exact this.measurable

theorem measurableSet_nrm3_eq_zero_union :
    MeasurableSet {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | nrm3 p.1 = 0 ∨ nrm3 p.2 = 0} := by
  have h1 : MeasurableSet {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | nrm3 p.1 = 0} :=
    measurableSet_preimage (measurable_nrm3.comp measurable_fst)
      (measurableSet_singleton (0 : ℝ))
  have h2 : MeasurableSet {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | nrm3 p.2 = 0} :=
    measurableSet_preimage (measurable_nrm3.comp measurable_snd)
      (measurableSet_singleton (0 : ℝ))
  exact h1.union h2

theorem measurable_innerQ_pair :
    Measurable fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => innerQ p.1 p.2 := by
  unfold innerQ
  refine Measurable.ite measurableSet_nrm3_eq_zero_union measurable_const ?_
  refine Measurable.div ?_ ?_
  · exact Finset.measurable_sum _ (fun a _ =>
      ((continuous_apply a).comp continuous_fst |>.measurable.mul
        ((continuous_apply a).comp continuous_snd |>.measurable)))
  · exact (measurable_nrm3.comp measurable_fst).mul (measurable_nrm3.comp measurable_snd)

theorem abs_innerQ_le_one (x z : Fin 3 → ℝ) : |innerQ x z| ≤ 1 := by
  unfold innerQ
  split_ifs with h
  · simp
  · have hx : nrm3 x ≠ 0 := fun e => h (Or.inl e)
    have hz : nrm3 z ≠ 0 := fun e => h (Or.inr e)
    have hsumnn : (0:ℝ) ≤ ∑ a : Fin 3, (x a) ^ 2 :=
      Finset.sum_nonneg (fun a _ => sq_nonneg (x a))
    have hsunnz : (0:ℝ) ≤ ∑ a : Fin 3, (z a) ^ 2 :=
      Finset.sum_nonneg (fun a _ => sq_nonneg (z a))
    have hx2 : nrm3 x ^ 2 = ∑ a, (x a) ^ 2 := Real.sq_sqrt hsumnn
    have hz2 : nrm3 z ^ 2 = ∑ a, (z a) ^ 2 := Real.sq_sqrt hsunnz
    have hcschwarz : (∑ a : Fin 3, x a * z a) ^ 2 ≤ (nrm3 x) ^ 2 * (nrm3 z) ^ 2 := by
      rw [hx2, hz2]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hnum : |∑ a : Fin 3, x a * z a| ≤ nrm3 x * nrm3 z := by
      have hsr : √((∑ a : Fin 3, x a * z a) ^ 2) ≤ √((nrm3 x) ^ 2 * (nrm3 z) ^ 2) :=
        Real.sqrt_le_sqrt hcschwarz
      have hnxsq : √(nrm3 x ^ 2) = nrm3 x := Real.sqrt_sq (Real.sqrt_nonneg _)
      have hnzsq : √(nrm3 z ^ 2) = nrm3 z := Real.sqrt_sq (Real.sqrt_nonneg _)
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg _), hnxsq, hnzsq] at hsr
      exact hsr
    have hnx : 0 < nrm3 x := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)
    have hnz : 0 < nrm3 z := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    have habsmul : |nrm3 x * nrm3 z| = nrm3 x * nrm3 z :=
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc |(∑ a, x a * z a) / (nrm3 x * nrm3 z)|
        = |∑ a, x a * z a| / (nrm3 x * nrm3 z) := by
          rw [abs_div, habsmul]
      _ ≤ 1 := by
          rw [div_le_one (mul_pos hnx hnz)]
          exact hnum

theorem innerQ_ne_zero (x z : Fin 3 → ℝ) (hx : nrm3 x ≠ 0) (hz : nrm3 z ≠ 0) :
    innerQ x z = (∑ a, x a * z a)/(nrm3 x * nrm3 z) := by
  unfold innerQ
  rw [if_neg (not_or.mpr ⟨hx, hz⟩)]

abbrev EU3k (k : ℕ) := EuclideanSpace ℝ (Fin 3 × Fin k)

def Gmap (t : EuclideanSpace ℝ (Fin 3 × Fin 2)) : ℝ :=
  innerQ (fun a => t (a, 0)) (fun a => t (a, 1))

theorem measurable_Gmap : Measurable Gmap := by
  have h : Gmap = (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => innerQ p.1 p.2) ∘
      (fun t : EU3k 2 => ((fun a => t (a, 0)), (fun a => t (a, 1)))) := rfl
  rw [h]
  exact measurable_innerQ_pair.comp
    (Measurable.prodMk (measurable_pi_lambda _ (fun a => by fun_prop))
      (measurable_pi_lambda _ (fun a => by fun_prop)))

def Hmap (c s : ℝ) (p : Fin 3 → ℝ × ℝ) : ℝ :=
  innerQ (fun a => (p a).1) (fun a => zcoord c s p a)

theorem measurable_Hmap (c s : ℝ) : Measurable (Hmap c s) := by
  have h : Hmap c s = (fun pq : (Fin 3 → ℝ) × (Fin 3 → ℝ) => innerQ pq.1 pq.2) ∘
      (fun p : Fin 3 → ℝ × ℝ => ((fun a => (p a).1), (fun a => zcoord c s p a))) := rfl
  rw [h]
  exact measurable_innerQ_pair.comp (Measurable.prodMk
    (measurable_pi_lambda _ (fun a => by fun_prop))
    (measurable_pi_lambda _ (fun a => by unfold zcoord; fun_prop)))

theorem psiMat_coord_eval (c s : ℝ) (w : Fin 3 × Fin 2 → ℝ) (a : Fin 3) :
    (BrickE.toEuclideanCLM' (psiMat c s) (WithLp.toLp 2 w)) (a, 0) = w (a, 0) ∧
    (BrickE.toEuclideanCLM' (psiMat c s) (WithLp.toLp 2 w)) (a, 1)
      = c * w (a, 0) + s * w (a, 1) := by
  have happ : ∀ q',
      ((BrickE.toEuclideanCLM' (psiMat c s)) (WithLp.toLp 2 w)) (a, q')
        = (psiMat c s *ᵥ w) (a, q') := by
    intro q'
    rw [BrickE.toEuclideanCLM'_apply, BrickE.ofLp_toEuclideanLin]
  obtain ⟨h0, h1⟩ := BrickE.psiMat_mulVec_pair c s w a
  exact ⟨by rw [happ, h0], by rw [happ, h1]⟩

theorem int_psi_chain (c s : ℝ) :
    ∫ t : EU3k 2, Gmap t ∂((stdGaussian (EU3k 2)).map (BrickE.toEuclideanCLM' (psiMat c s)))
      = ∫ p : Fin 3 → ℝ × ℝ, innerQ (fun a => (p a).1) (fun a => zcoord c s p a) ∂μ3 := by
  have hG : AEStronglyMeasurable Gmap
      ((stdGaussian (EU3k 2)).map (BrickE.toEuclideanCLM' (psiMat c s))) :=
    measurable_Gmap.aestronglyMeasurable
  rw [integral_map (by fun_prop) hG]
  rw [← map_pi_eq_stdGaussian (ι := Fin 3 × Fin 2)]
  have hΨmeas : Measurable (BrickE.toEuclideanCLM' (psiMat c s)) := by fun_prop
  have hcompmeas : Measurable (fun x : EU3k 2 => Gmap ((BrickE.toEuclideanCLM' (psiMat c s)) x)) :=
    measurable_Gmap.comp hΨmeas
  rw [integral_map (by fun_prop) hcompmeas.aestronglyMeasurable]
  have hH : AEStronglyMeasurable (fun p => innerQ (fun a => (p a).1) (fun a => zcoord c s p a)) μ3 := by
    rw [show (fun p => innerQ (fun a => (p a).1) (fun a => zcoord c s p a)) = Hmap c s from rfl]
    exact (measurable_Hmap c s).aestronglyMeasurable
  rw [← measurePreserving_pi6_mu3.map_eq] at hH
  rw [← (measurePreserving_pi6_mu3.map_eq), integral_map e3ME.measurable.aemeasurable hH]
  refine integral_congr_ae ?_
  refine Eventually.of_forall fun w => ?_
  show Gmap ((BrickE.toEuclideanCLM' (psiMat c s)) (WithLp.toLp 2 w))
    = Hmap c s (e3ME w)
  unfold Gmap Hmap
  have he0 : (fun a => (BrickE.toEuclideanCLM' (psiMat c s) (WithLp.toLp 2 w)) (a, 0))
      = fun a => w (a, 0) := funext (fun a => (psiMat_coord_eval c s w a).1)
  have he1 : (fun a => (BrickE.toEuclideanCLM' (psiMat c s) (WithLp.toLp 2 w)) (a, 1))
      = fun a => c * w (a, 0) + s * w (a, 1) := funext (fun a => (psiMat_coord_eval c s w a).2)
  rw [he0, he1, e3ME_zcoord_form]

theorem phiMat_mulVec_pair {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (w : Fin 3 × Fin n → ℝ) (a : Fin 3) :
    (phiMat u v *ᵥ w) (a, 0) = ∑ k : Fin n, u.ofLp k * w (a, k) ∧
    (phiMat u v *ᵥ w) (a, 1) = ∑ k : Fin n, v.ofLp k * w (a, k) := by
  have key : ∀ q : Fin 2, (phiMat u v *ᵥ w) (a, q)
      = ∑ k : Fin n, phiMat u v (a, q) (a, k) * w (a, k) := by
    intro q
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_eq_single a ?_ ?_
    · intro b _ hne
      have hzero : ∀ k : Fin n, phiMat u v (a, q) (b, k) * w (b, k) = 0 := by
        intro k
        have hent : phiMat u v (a, q) (b, k) = 0 := by
          unfold phiMat
          rw [Matrix.of_apply]
          exact if_neg (fun h => hne h.symm)
        rw [hent, zero_mul]
      simp only [hzero, Finset.sum_const_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hentry0 : ∀ k : Fin n, phiMat u v (a, 0) (a, k) = u.ofLp k := by
    intro k
    simp [phiMat]
  have hentry1 : ∀ k : Fin n, phiMat u v (a, 1) (a, k) = v.ofLp k := by
    intro k
    simp [phiMat]
  constructor
  · rw [key 0]
    exact Finset.sum_congr rfl (fun k _ => by rw [hentry0 k])
  · rw [key 1]
    exact Finset.sum_congr rfl (fun k _ => by rw [hentry1 k])

theorem psiMat_coord_eval_ofLp (c s : ℝ) (t : EU3k 2) (a : Fin 3) :
    ((BrickE.toEuclideanCLM' (psiMat c s)) t) (a, 0) = t (a, 0) ∧
    ((BrickE.toEuclideanCLM' (psiMat c s)) t) (a, 1) = c * t (a, 0) + s * t (a, 1) := by
  have happ : ∀ q', ((BrickE.toEuclideanCLM' (psiMat c s)) t) (a, q')
      = (psiMat c s *ᵥ t.ofLp) (a, q') := by
    intro q'
    rw [BrickE.toEuclideanCLM'_apply, BrickE.ofLp_toEuclideanLin]
  obtain ⟨h0, h1⟩ := BrickE.psiMat_mulVec_pair c s t.ofLp a
  exact ⟨by rw [happ, h0], by rw [happ, h1]⟩

def Vvec {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (ω : EU3k n) (a : Fin 3) : ℝ :=
  ∑ k : Fin n, u.ofLp k * ω (a, k)

theorem Vvec_measurable {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (a : Fin 3) :
    Measurable fun ω : EU3k n => Vvec u ω a := by
  unfold Vvec
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact measurable_const.mul (by fun_prop)

def phiclm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (i j : Fin n) :
    EU3k n →L[ℝ] EU3k 2 :=
  BrickE.toEuclideanCLM' (phiMat (gramVec X hX i) (gramVec X hX j))

theorem phiclm_pair {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i j : Fin n) (ω : EU3k n) (a : Fin 3) :
    ((phiclm X hX i j) ω) (a, 0) = Vvec (gramVec X hX i) ω a ∧
    ((phiclm X hX i j) ω) (a, 1) = Vvec (gramVec X hX j) ω a := by
  have happ : ∀ q', ((phiclm X hX i j) ω) (a, q')
      = (phiMat (gramVec X hX i) (gramVec X hX j) *ᵥ ω.ofLp) (a, q') := by
    intro q'
    show ((BrickE.toEuclideanCLM' (phiMat (gramVec X hX i) (gramVec X hX j))) ω) (a, q')
        = (phiMat (gramVec X hX i) (gramVec X hX j) *ᵥ ω.ofLp) (a, q')
    rw [BrickE.toEuclideanCLM'_apply, BrickE.ofLp_toEuclideanLin]
  obtain ⟨h0, h1⟩ := phiMat_mulVec_pair (gramVec X hX i) (gramVec X hX j) ω.ofLp a
  show ((phiclm X hX i j) ω) (a, 0) = Vvec (gramVec X hX i) ω a ∧
    ((phiclm X hX i j) ω) (a, 1) = Vvec (gramVec X hX j) ω a
  unfold Vvec
  exact ⟨by rw [happ 0, h0], by rw [happ 1, h1]⟩

theorem edge_expectation {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (hdiag : (∀ i, X i i = 1)) (i j : Fin n) :
    ∫ ω : EU3k n, Gmap ((phiclm X hX i j) ω) ∂(stdGaussian (EU3k n))
      = bovInt (X i j) := by
  have hΦmeas : Measurable (phiclm X hX i j) := by fun_prop
  have hG : AEStronglyMeasurable Gmap ((stdGaussian (EU3k n)).map (phiclm X hX i j)) :=
    measurable_Gmap.aestronglyMeasurable
  rw [← integral_map hΦmeas.aemeasurable hG]
  have hu : ‖gramVec X hX i‖ = 1 := norm_gramVec hdiag i
  have hv : ‖gramVec X hX j‖ = 1 := norm_gramVec hdiag j
  have hc : ⟪gramVec X hX i, gramVec X hX j⟫ = X i j := inner_gramVec i j
  have hssq : (Real.sqrt (1 - (X i j) ^ 2)) ^ 2 = 1 - (X i j) ^ 2 := by
    have habs := abs_X_le_one (n := n) (X := X) (hX := hX) hdiag i j
    have hsquared : (X i j) ^ 2 ≤ 1 := by
      have h1 : -1 ≤ X i j := (abs_le.mp habs).1
      have h2 : X i j ≤ 1 := (abs_le.mp habs).2
      nlinarith [sq_nonneg (X i j)]
    exact Real.sq_sqrt (by linarith)
  rw [show (stdGaussian (EU3k n)).map (phiclm X hX i j)
      = (stdGaussian (EU3k n)).map
        (BrickE.toEuclideanCLM' (phiMat (gramVec X hX i) (gramVec X hX j))) from rfl]
  rw [BrickE.margin_pushforward_eq' (gramVec X hX i) (gramVec X hX j) hu hv
    (X i j) (Real.sqrt (1 - (X i j) ^ 2)) hc hssq]
  rw [int_psi_chain]
  have h6 : ∀ r q : ℝ, 0 < r → 0 < q →
      ∫ p : Fin 3 → ℝ × ℝ, (∑ a, (p a).1 * zcoord (X i j) (Real.sqrt (1 - (X i j) ^ 2)) p a)
          * Real.exp (-(r ^ 2 * ∑ a, ((p a).1) ^ 2)
            - q ^ 2 * ∑ a, (zcoord (X i j) (Real.sqrt (1 - (X i j) ^ 2)) p a) ^ 2) ∂μ3
        = 3 * (X i j) * (Real.sqrt (Dbloch r q (X i j))⁻¹) ^ 5 :=
    fun r q hr hq =>
      sixdim_weighted_inner r q (X i j) (Real.sqrt (1 - (X i j) ^ 2)) hssq hr hq
        (cross_moment r q (X i j) (Real.sqrt (1 - (X i j) ^ 2)) hssq hr hq)
  exact bov_expectation_eq_bovInt (X i j) (Real.sqrt (1 - (X i j) ^ 2)) hssq h6

theorem null_Vvec_coord {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (hdiag : (∀ i, X i i = 1)) (i : Fin n) :
    (stdGaussian (EU3k n)) {ω : EU3k n | Vvec (gramVec X hX i) ω 0 = 0} = 0 := by
  haveI : NullSingletonClass (gaussianReal (0 : ℝ) 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hcoord_meas : MeasurableSet {t : EU3k 2 | t (0, 0) = 0} :=
    measurableSet_preimage (by fun_prop) (measurableSet_singleton (0 : ℝ))
  have hset : {ω : EU3k n | Vvec (gramVec X hX i) ω 0 = 0}
      = (phiclm X hX i i) ⁻¹' {t : EU3k 2 | t (0, 0) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    show (Vvec (gramVec X hX i) ω 0 = 0) ↔ (((phiclm X hX i i) ω) (0, 0) = 0)
    rw [← (phiclm_pair i i ω 0).1]
  rw [hset, ← Measure.map_apply (by fun_prop) hcoord_meas]
  have hu : ‖gramVec X hX i‖ = 1 := norm_gramVec hdiag i
  have hc : ⟪gramVec X hX i, gramVec X hX i⟫ = X i i := inner_gramVec i i
  have hssq : (0 : ℝ) ^ 2 = 1 - ((X i i) ^ 2) := by
    rw [hdiag i]
    norm_num
  unfold phiclm
  rw [BrickE.margin_pushforward_eq' (gramVec X hX i) (gramVec X hX i) hu hu (X i i) 0 hc hssq]
  rw [Measure.map_apply (by fun_prop : Measurable (BrickE.toEuclideanCLM' (psiMat (X i i) 0)))
      hcoord_meas]
  have hpre : (BrickE.toEuclideanCLM' (psiMat (X i i) 0)) ⁻¹' {t : EU3k 2 | t (0, 0) = 0}
      = {w : EU3k 2 | w (0, 0) = 0} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [(psiMat_coord_eval_ofLp (X i i) 0 w 0).1]
  rw [hpre, ← map_pi_eq_stdGaussian (ι := Fin 3 × Fin 2),
    Measure.map_apply (by fun_prop : Measurable (WithLp.toLp 2 : (Fin 3 × Fin 2 → ℝ) → EU3k 2))
      hcoord_meas]
  have hpr : ((WithLp.toLp 2 : (Fin 3 × Fin 2 → ℝ) → EU3k 2) ⁻¹' {w : EU3k 2 | w (0, 0) = 0})
      = {w' : Fin 3 × Fin 2 → ℝ | w' (0, 0) = 0} := rfl
  rw [hpr]
  exact Measure.pi_eval_preimage_null
    (μ := fun _ : Fin 3 × Fin 2 => gaussianReal (0 : ℝ) 1) (i := (0, 0))
    ((Set.subsingleton_singleton).measure_zero (gaussianReal (0 : ℝ) 1))

theorem measurable_Vvec {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    Measurable fun ω : EU3k n => Vvec u ω :=
  measurable_pi_lambda _ (fun a => Vvec_measurable u a)

theorem ae_good_set {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (hdiag : (∀ i, X i i = 1)) :
    ∀ᵐ ω ∂(stdGaussian (EU3k n)), ∀ i : Fin n, nrm3 (Vvec (gramVec X hX i) ω) ≠ 0 := by
  rw [ae_all_iff]
  intro i
  rw [MeasureTheory.ae_iff]
  simp only [ne_eq, not_not]
  refine measure_mono_null ?_ (null_Vvec_coord (n := n) (X := X) (hX := hX) hdiag i)
  intro ω hω
  exact (nrm3_eq_zero_iff (Vvec (gramVec X hX i) ω)).mp hω 0

theorem exists_good_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) {B : ℝ} (h : ∫ ω, f ω ∂μ ≤ B)
    {A : Set α} (hAmeas : MeasurableSet A) (hA : ∀ᵐ ω ∂μ, ω ∈ A) : ∃ ω ∈ A, f ω ≤ B := by
  by_contra hcon
  push Not at hcon
  have hnn : 0 ≤ᵐ[μ] fun ω => f ω - B :=
    hA.mono (fun ω hω => sub_nonneg.mpr (hcon ω hω).le)
  have hint : Integrable (fun ω => f ω - B) μ := hf.sub (integrable_const B)
  have hpos : 0 < ∫ ω, f ω - B ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    have hsubset : A ⊆ Function.support fun ω => f ω - B := by
      intro ω hω
      show (fun ω => f ω - B) ω ≠ 0
      exact ne_of_gt (sub_pos.mpr (hcon ω hω))
    have hmono : μ A ≤ μ (Function.support fun ω => f ω - B) := measure_mono hsubset
    have hcompl : μ Aᶜ = 0 := by
      rw [show Aᶜ = {ω : α | ¬ (ω ∈ A)} from rfl, ← MeasureTheory.ae_iff]
      exact hA
    have hAfull : μ A = 1 := by
      have h' : μ A + μ Aᶜ = μ Set.univ := measure_add_measure_compl hAmeas
      rw [hcompl, measure_univ] at h'
      simpa using h'
    have hfullsup : 1 ≤ μ (Function.support fun ω => f ω - B) := by
      have hmono2 : μ A ≤ μ (Function.support fun ω => f ω - B) := measure_mono hsubset
      rw [hAfull] at hmono2
      exact hmono2
    have : (0:ℝ≥0∞) < μ (Function.support fun ω => f ω - B) :=
      lt_of_lt_of_le zero_lt_one hfullsup
    exact this
  have hval : ∫ ω, f ω - B ∂μ = ∫ ω, f ω ∂μ - B := by
    rw [integral_sub hf (integrable_const B)]
    simp [integral_const]
  rw [hval] at hpos
  linarith

theorem good_set_measurable {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef} :
    MeasurableSet {ω : EU3k n | ∀ i : Fin n, nrm3 (Vvec (gramVec X hX i) ω) ≠ 0} := by
  have hs : {ω : EU3k n | ∀ i : Fin n, nrm3 (Vvec (gramVec X hX i) ω) ≠ 0}
      = ⋂ i : Fin n, {ω : EU3k n | nrm3 (Vvec (gramVec X hX i) ω) ≠ 0} := by
    ext ω
    simp
  rw [hs]
  refine MeasurableSet.iInter (fun i => ?_)
  have hm : Measurable fun ω : EU3k n => nrm3 (Vvec (gramVec X hX i) ω) :=
    measurable_nrm3.comp (measurable_Vvec (gramVec X hX i))
  have hmset : MeasurableSet {ω : EU3k n | nrm3 (Vvec (gramVec X hX i) ω) = 0} :=
    measurableSet_preimage hm (measurableSet_singleton (0 : ℝ))
  exact hmset.compl

def edgeInner {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i j : Fin n) (ω : EU3k n) : ℝ := Gmap ((phiclm X hX i j) ω)

theorem edgeInner_measurable {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i j : Fin n) : Measurable (edgeInner (n := n) (X := X) (hX := hX) i j) := by
  unfold edgeInner
  exact measurable_Gmap.comp (by fun_prop)

theorem edgeInner_abs_le_one {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i j : Fin n) (ω : EU3k n) : |edgeInner (n := n) (X := X) (hX := hX) i j ω| ≤ 1 := by
  unfold edgeInner Gmap
  exact abs_innerQ_le_one _ _

theorem edgeInner_integrable {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i j : Fin n) :
    Integrable (edgeInner (n := n) (X := X) (hX := hX) i j) (stdGaussian (EU3k n)) := by
  haveI : IsProbabilityMeasure (stdGaussian (EU3k n)) := inferInstance
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((edgeInner_measurable (n := n) (X := X) (hX := hX) i j).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact edgeInner_abs_le_one (n := n) (X := X) (hX := hX) i j ω

theorem edgeInner_eq {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (i j : Fin n) (ω : EU3k n) :
    edgeInner (n := n) (X := X) (hX := hX) i j ω
      = innerQ (Vvec (gramVec X hX i) ω) (Vvec (gramVec X hX j) ω) := by
  unfold edgeInner Gmap
  have h0 : (fun a => ((phiclm X hX i j) ω) (a, 0)) = Vvec (gramVec X hX i) ω :=
    funext (fun a => (phiclm_pair i j ω a).1)
  have h1 : (fun a => ((phiclm X hX i j) ω) (a, 1)) = Vvec (gramVec X hX j) ω :=
    funext (fun a => (phiclm_pair i j ω a).2)
  rw [h0, h1]

theorem expectation_weighted_sum {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (hdiag : (∀ i, X i i = 1)) (ι : Type*) [Fintype ι]
    (ends : ι → Fin n × Fin n) (w : ι → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∫ ω : EU3k n, (∑ e : ι, w e * edgeInner (n := n) (X := X) (hX := hX) (ends e).1 (ends e).2 ω)
        ∂(stdGaussian (EU3k n))
      ≤ 0.046 * (∑ e : ι, w e) + 0.954 * (∑ e : ι, w e * X (ends e).1 (ends e).2) := by
  have hI : ∀ e : ι, Integrable
      (fun ω => w e * edgeInner (n := n) (X := X) (hX := hX) (ends e).1 (ends e).2 ω)
      (stdGaussian (EU3k n)) :=
    fun e => Integrable.const_mul
      (edgeInner_integrable (n := n) (X := X) (hX := hX) (ends e).1 (ends e).2) (w e)
  have hsum : ∫ ω : EU3k n,
      (∑ e : ι, w e * edgeInner (n := n) (X := X) (hX := hX) (ends e).1 (ends e).2 ω)
        ∂(stdGaussian (EU3k n))
      = ∑ e : ι, w e * bovInt (X (ends e).1 (ends e).2) := by
    rw [MeasureTheory.integral_finset_sum _ (fun e _ => hI e)]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [integral_const_mul]
    rw [show (∫ ω : EU3k n, edgeInner (n := n) (X := X) (hX := hX) (ends e).1 (ends e).2 ω
        ∂(stdGaussian (EU3k n))) = ∫ ω : EU3k n, Gmap ((phiclm X hX (ends e).1 (ends e).2) ω)
        ∂(stdGaussian (EU3k n)) from rfl]
    rw [edge_expectation hdiag (ends e).1 (ends e).2]
  rw [hsum]
  have hbound : ∀ e : ι, w e * bovInt (X (ends e).1 (ends e).2)
      ≤ w e * (0.046 + 0.954 * X (ends e).1 (ends e).2) := by
    intro e
    refine mul_le_mul_of_nonneg_left ?_ (hw e)
    have hc_abs := abs_X_le_one (n := n) (X := X) (hX := hX) hdiag (ends e).1 (ends e).2
    have hc : X (ends e).1 (ends e).2 ∈ Set.Icc (-1) 1 := ⟨neg_le_of_abs_le hc_abs, le_of_abs_le hc_abs⟩
    exact BrickD.bovInt_le_linear (X (ends e).1 (ends e).2) hc C1 C1i C2 C2i C3 C3i
  have hsumle : ∑ e : ι, w e * bovInt (X (ends e).1 (ends e).2)
      ≤ ∑ e : ι, w e * (0.046 + 0.954 * X (ends e).1 (ends e).2) :=
    Finset.sum_le_sum (fun e _ => hbound e)
  refine hsumle.trans ?_
  have hshape : ∀ e : ι, w e * (0.046 + 0.954 * X (ends e).1 (ends e).2)
      = (0.046 * w e + 0.954 * (w e * X (ends e).1 (ends e).2)) := fun e => by ring
  rw [Finset.sum_congr rfl (fun e _ => hshape e), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

theorem good_point_generic {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {hX : X.PosSemidef}
    (hdiag : (∀ i, X i i = 1)) (ι : Type*) [Fintype ι]
    (ends : ι → Fin n × Fin n) (w : ι → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ r : Fin n → Fin 3 → ℝ, (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
      (∑ e : ι, w e * (∑ a : Fin 3, r (ends e).1 a * r (ends e).2 a))
        ≤ 0.046 * (∑ e : ι, w e) + 0.954 * (∑ e : ι, w e * X (ends e).1 (ends e).2) := by
  have hI : Integrable
      (fun ω : EU3k n => ∑ e : ι, w e * edgeInner (n := n) (X := X) (hX := hX) (ends e).1 (ends e).2 ω)
      (stdGaussian (EU3k n)) := by
    refine integrable_finset_sum _ (fun e _ => ?_)
    exact Integrable.const_mul
      (edgeInner_integrable (n := n) (X := X) (hX := hX) (ends e).1 (ends e).2) (w e)
  have hle := expectation_weighted_sum (n := n) (X := X) (hX := hX) hdiag ι ends w hw
  obtain ⟨ω, hωA, hωle⟩ := exists_good_le (μ := stdGaussian (EU3k n)) hI hle
    (good_set_measurable (n := n) (X := X) (hX := hX))
    (ae_good_set (n := n) (X := X) (hX := hX) hdiag)
  have hωgood : ∀ i : Fin n, nrm3 (Vvec (gramVec X hX i) ω) ≠ 0 := hωA
  
  set r : Fin n → Fin 3 → ℝ :=
    fun i => fun a => Vvec (gramVec X hX i) ω a / nrm3 (Vvec (gramVec X hX i) ω) with hr
  have hunit : ∀ i : Fin n, ∑ a : Fin 3, (r i a) ^ 2 = 1 := by
    intro i
    have hnrm : nrm3 (Vvec (gramVec X hX i) ω) ≠ 0 := hωgood i
    have hnrm2 : nrm3 (Vvec (gramVec X hX i) ω) ^ 2 = ∑ a : Fin 3, (Vvec (gramVec X hX i) ω a) ^ 2 := by
      rw [nrm3]
      exact Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _))
    have hstep : ∀ a : Fin 3, (r i a) ^ 2 = (Vvec (gramVec X hX i) ω a) ^ 2 / (nrm3 (Vvec (gramVec X hX i) ω)) ^ 2 := by
      intro a
      rw [hr]
      rw [div_pow]
    rw [Finset.sum_congr rfl (fun a _ => hstep a)]
    rw [← Finset.sum_div]
    have hz := pow_ne_zero 2 hnrm
    rw [hnrm2] at hz
    rw [hnrm2]
    exact div_self hz
  have hval : ∀ e : ι, (∑ a : Fin 3, r (ends e).1 a * r (ends e).2 a)
      = innerQ (Vvec (gramVec X hX (ends e).1) ω) (Vvec (gramVec X hX (ends e).2) ω) := by
    intro e
    have hei : nrm3 (Vvec (gramVec X hX (ends e).1) ω) ≠ 0 := hωgood (ends e).1
    have hej : nrm3 (Vvec (gramVec X hX (ends e).2) ω) ≠ 0 := hωgood (ends e).2
    unfold innerQ
    rw [if_neg (not_or.mpr ⟨hei, hej⟩)]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hr, div_mul_div_comm]
  refine ⟨r, hunit, ?_⟩
  have hfinal : (∑ e : ι, w e * (∑ a : Fin 3, r (ends e).1 a * r (ends e).2 a))
      = ∑ e : ι, w e * edgeInner (n := n) (X := X) (hX := hX) (ends e).1 (ends e).2 ω := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hval e, edgeInner_eq]
  rw [hfinal]
  exact hωle

end Asm
end Rank3Gaussian
end

theorem solution (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) :
    ∃ F : ℝ → ℝ, (∃ c : ℕ → ℝ, (∀ k, 0 ≤ c k) ∧ Summable c ∧ (∑' k, c k) = 1 ∧
      8 / (3 * Real.pi) ≤ c 0 ∧ 4 / (15 * Real.pi) ≤ c 1 ∧
      ∀ t : ℝ, -1 ≤ t → t < 1 → F t = ∑' k, c k * t ^ (2 * k + 1)) ∧
      ∀ w : QuantumMaxCutEnergy.Weights n,
        (∃ r : Fin n → Fin 3 → ℝ, (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
          (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
            (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) ≤
          0.046 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ)) +
          0.954 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) * X e.val.1 e.val.2)) := by
  obtain ⟨F, ⟨c, hc0, hcSum, hct, hc0b, hc1b, hseries⟩⟩ := Rank3Gaussian.exists_F_series_witness
  refine ⟨F, ⟨c, hc0, hcSum, hct, hc0b, hc1b, hseries⟩, ?_⟩
  intro w
  have hgen := Rank3Gaussian.Asm.good_point_generic (n := n) (X := X) (hX := hX) hdiag
    (ι := QuantumMaxCutEnergy.Edge n) (ends := fun e => (e.val.1, e.val.2))
    (w := fun e => (w e : ℝ)) (hw := fun e => by positivity)
  exact hgen
