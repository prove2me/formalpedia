-- Prove2me | solution 1 for RobustOpt2009.SDPApproximation.proposition_B_4_12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:06:30.160973+00:00
-- url     : https://prove2.me/submissions/93552e93-b2f1-4937-a736-ef65b7de46e4

import Mathlib

open Matrix MeasureTheory ProbabilityTheory Real

namespace S192B412

/-- `E|X| ^ 2 = 2/π` for a standard real Gaussian. -/
lemma absMomentReal : (∫ x, |x| ∂(gaussianReal 0 1)) ^ 2 = 2 / π := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h1 : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|) =
      fun x => (fun r : ℝ => (√(2 * π))⁻¹ * (r ^ (1:ℝ) * rexp (-(1/2) * r ^ (2:ℝ)))) |x| := by
    funext x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero, rpow_one,
      rpow_two, sq_abs]
    ring_nf
  rw [h1, integral_comp_abs (f := fun r : ℝ => (√(2 * π))⁻¹ * (r ^ (1:ℝ) * rexp (-(1/2) * r ^ (2:ℝ)))), integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  norm_num
  simp only [mul_pow, inv_pow, sq_sqrt pi_pos.le, sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  field_simp

/-- `E|w| = √π / 2` for a standard complex Gaussian. -/
lemma absMomentComplex :
    ∫ u, ‖(⟨u.1, u.2⟩ : ℂ)‖ ∂((gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2))) = √π / 2 := by
  have hv : ((1/2 : NNReal) : ℝ) = 1/2 := by norm_num
  rw [gaussianReal_of_var_ne_zero _ (by norm_num), prod_withDensity
    (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top)]
  rw [← Measure.volume_eq_prod, ← integral_comp_polarCoord_symm, polarCoord_target]
  have h2 : ∀ p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π,
      p.1 • ((gaussianPDF 0 (1/2) (polarCoord.symm p).1 * gaussianPDF 0 (1/2)
        (polarCoord.symm p).2).toReal • ‖(⟨(polarCoord.symm p).1, (polarCoord.symm p).2⟩ : ℂ)‖)
      = (fun r : ℝ => (π)⁻¹ * (r ^ (2:ℝ) * rexp (-1 * r ^ (2:ℝ)))) p.1 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [Set.mem_Ioi] at hr
    simp only [polarCoord_symm_apply, gaussianPDF, smul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    have hn : ‖(⟨r * cos θ, r * sin θ⟩ : ℂ)‖ = r := by
      rw [Complex.norm_def, Complex.normSq_mk]
      have : r * cos θ * (r * cos θ) + r * sin θ * (r * sin θ) = r ^ 2 := by
        have := sin_sq_add_cos_sq θ; nlinarith
      rw [this, sqrt_sq hr.le]
    rw [hn]
    simp only [gaussianPDFReal, hv, sub_zero, rpow_two]
    have hs : √(2 * π * (1/2)) = √π := by ring_nf
    rw [hs, ← mul_assoc, ← mul_assoc]
    have e : rexp (-(r * cos θ) ^ 2 / (2 * (1 / 2))) * rexp (-(r * sin θ) ^ 2 / (2 * (1 / 2)))
        = rexp (-1 * r ^ 2) := by
      rw [← Real.exp_add]; congr 1
      have := sin_sq_add_cos_sq θ; ring_nf; nlinarith
    have hpi : (√π)⁻¹ * (√π)⁻¹ = π⁻¹ := by
      rw [← mul_inv, mul_self_sqrt pi_pos.le]
    rw [← hpi, ← e]; ring
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) h2,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_fun_fst (f := fun r : ℝ => π⁻¹ * (r ^ (2:ℝ) * rexp (-1 * r ^ (2:ℝ)))), integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    volume_Ioo, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [pi_pos])]
  have : ((2:ℝ) + 1) / 2 = 1/2 + 1 := by norm_num
  rw [this, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  field_simp
  ring

end S192B412


open Matrix MeasureTheory ProbabilityTheory Real Complex ComplexConjugate

namespace S192B412

noncomputable section

abbrev γR (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1

abbrev γC (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun _ => (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))

def zC {n : ℕ} (x : Fin n → ℝ × ℝ) : Fin n → ℂ := fun i => ⟨(x i).1, (x i).2⟩

lemma cont_dotR {n : ℕ} (p : Fin n → ℝ) : Continuous fun x : Fin n → ℝ => p ⬝ᵥ x := by
  simp only [dotProduct]; fun_prop

lemma cont_zC {n : ℕ} : Continuous (zC (n := n)) := by
  refine continuous_pi fun i => ?_
  have : (fun x : Fin n → ℝ × ℝ => zC x i) =
      fun x => Complex.equivRealProdCLM.symm (x i) := by
    funext x; rfl
  rw [this]; fun_prop

lemma cont_dotC {n : ℕ} (p : Fin n → ℂ) : Continuous fun x : Fin n → ℝ × ℝ => p ⬝ᵥ zC x := by
  have h := cont_zC (n := n)
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp h)

lemma cfR {n : ℕ} (d : Fin n → ℝ) :
    ∫ x, cexp (((d ⬝ᵥ x : ℝ) : ℂ) * I) ∂γR n = cexp (-((d ⬝ᵥ d : ℝ) : ℂ) / 2) := by
  have h : ∀ x : Fin n → ℝ, cexp (((d ⬝ᵥ x : ℝ) : ℂ) * I) =
      ∏ j, (fun j (t : ℝ) => cexp ((d j : ℂ) * t * I)) j (x j) := by
    intro x
    simp only [dotProduct, ofReal_sum, ofReal_mul, Finset.sum_mul, Complex.exp_sum]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (f := fun j (t : ℝ) => cexp ((d j : ℂ) * t * I))]
  have h2 : ∀ j, ∫ t, cexp ((d j : ℂ) * t * I) ∂(gaussianReal 0 1) =
      cexp (-((d j : ℂ) ^ 2) / 2) := by
    intro j
    rw [← charFun_apply_real, charFun_gaussianReal]
    congr 1; push_cast; ring
  simp_rw [h2, ← Complex.exp_sum]
  congr 1
  simp only [dotProduct, ofReal_sum, ofReal_mul, Finset.sum_div, ← Finset.sum_neg_distrib]
  congr 1; funext j; ring

lemma dualProd (L : StrongDual ℝ (ℝ × ℝ)) (u v : ℝ) : L (u, v) = L (1, 0) * u + L (0, 1) * v := by
  have : ((u, v) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm u, mul_comm v]

lemma lawR {n k : ℕ} (p m : Fin n → ℝ) (p' m' : Fin k → ℝ) (h1 : p ⬝ᵥ p = p' ⬝ᵥ p')
    (h2 : p ⬝ᵥ m = p' ⬝ᵥ m') (h3 : m ⬝ᵥ m = m' ⬝ᵥ m') :
    (γR n).map (fun x => (p ⬝ᵥ x, m ⬝ᵥ x)) = (γR k).map (fun y => (p' ⬝ᵥ y, m' ⬝ᵥ y)) := by
  have c1 : Continuous fun x : Fin n → ℝ => (p ⬝ᵥ x, m ⬝ᵥ x) :=
    (cont_dotR p).prodMk (cont_dotR m)
  have c2 : Continuous fun x : Fin k → ℝ => (p' ⬝ᵥ x, m' ⬝ᵥ x) :=
    (cont_dotR p').prodMk (cont_dotR m')
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply, integral_map c1.aemeasurable (by fun_prop),
    integral_map c2.aemeasurable (by fun_prop)]
  have e : ∀ {N : ℕ} (a b : Fin N → ℝ) (x : Fin N → ℝ),
      L (a ⬝ᵥ x, b ⬝ᵥ x) = (L (1, 0) • a + L (0, 1) • b) ⬝ᵥ x := by
    intro N a b x
    rw [dualProd, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  simp_rw [e, cfR]
  congr 4
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm m p, dotProduct_comm m' p', h1, h2, h3]

lemma intR {n k : ℕ} (p m : Fin n → ℝ) (p' m' : Fin k → ℝ) (h1 : p ⬝ᵥ p = p' ⬝ᵥ p')
    (h2 : p ⬝ᵥ m = p' ⬝ᵥ m') (h3 : m ⬝ᵥ m = m' ⬝ᵥ m') (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    ∫ x, f (p ⬝ᵥ x, m ⬝ᵥ x) ∂γR n = ∫ y, f (p' ⬝ᵥ y, m' ⬝ᵥ y) ∂γR k := by
  have c1 : Continuous fun x : Fin n → ℝ => (p ⬝ᵥ x, m ⬝ᵥ x) :=
    (cont_dotR p).prodMk (cont_dotR m)
  have c2 : Continuous fun x : Fin k → ℝ => (p' ⬝ᵥ x, m' ⬝ᵥ x) :=
    (cont_dotR p').prodMk (cont_dotR m')
  rw [← integral_map (f := f) c1.aemeasurable hf.aestronglyMeasurable,
    ← integral_map (f := f) c2.aemeasurable hf.aestronglyMeasurable, lawR p m p' m' h1 h2 h3]

lemma cfC {n : ℕ} (c : Fin n → ℂ) :
    ∫ x, cexp ((((c ⬝ᵥ zC x).re : ℝ) : ℂ) * I) ∂γC n =
      cexp (-((∑ i, normSq (c i) : ℝ) : ℂ) / 4) := by
  have h : ∀ x : Fin n → ℝ × ℝ, cexp ((((c ⬝ᵥ zC x).re : ℝ) : ℂ) * I) =
      ∏ j, (fun j (t : ℝ × ℝ) => cexp (((c j).re : ℂ) * t.1 * I) *
        cexp ((-(c j).im : ℝ) * t.2 * I)) j (x j) := by
    intro x
    simp only [dotProduct, re_sum, ofReal_sum, Finset.sum_mul, Complex.exp_sum, zC, mul_re]
    congr 1; funext j
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (f := fun j (t : ℝ × ℝ) => cexp (((c j).re : ℂ) * t.1 * I) *
        cexp ((-(c j).im : ℝ) * t.2 * I))]
  have h2 : ∀ j, ∫ t, cexp (((c j).re : ℂ) * t.1 * I) * cexp ((-(c j).im : ℝ) * t.2 * I)
      ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) =
      cexp (-((normSq (c j) : ℝ) : ℂ) / 4) := by
    intro j
    rw [integral_prod_mul (f := fun t : ℝ => cexp (((c j).re : ℂ) * t * I))
      (g := fun t : ℝ => cexp ((-(c j).im : ℝ) * t * I)), ← charFun_apply_real,
      ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add]
    congr 1; rw [normSq_apply]; push_cast; ring
  simp_rw [h2, ← Complex.exp_sum]
  congr 1
  simp only [ofReal_sum, Finset.sum_div, ← Finset.sum_neg_distrib]

lemma dualProdC (L : StrongDual ℝ (ℂ × ℂ)) (u v : ℂ) :
    L (u, v) = ((⟨L (1, 0), -L (I, 0)⟩ : ℂ) * u + (⟨L (0, 1), -L (0, I)⟩ : ℂ) * v).re := by
  have : ((u, v) : ℂ × ℂ) = u.re • ((1 : ℂ), (0 : ℂ)) + u.im • ((I : ℂ), (0 : ℂ)) +
      (v.re • ((0 : ℂ), (1 : ℂ)) + v.im • ((0 : ℂ), (I : ℂ))) := by
    ext <;> simp [Complex.ext_iff]
  rw [this, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  simp only [smul_eq_mul, add_re, mul_re]
  ring

lemma sumNormSq {n : ℕ} (a b : ℂ) (p m : Fin n → ℂ) :
    ∑ i, normSq ((a • p + b • m) i) = normSq a * ∑ i, normSq (p i) +
      normSq b * ∑ i, normSq (m i) + 2 * (a * conj b * (p ⬝ᵥ star m)).re := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, normSq_add, normSq_mul,
    Finset.sum_add_distrib, Finset.mul_sum, dotProduct, re_sum, Pi.star_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 2
  simp only [RCLike.star_def]
  ring

lemma lawC {n k : ℕ} (p m : Fin n → ℂ) (p' m' : Fin k → ℂ)
    (h1 : ∑ i, normSq (p i) = ∑ i, normSq (p' i))
    (h2 : p ⬝ᵥ star m = p' ⬝ᵥ star m') (h3 : ∑ i, normSq (m i) = ∑ i, normSq (m' i)) :
    (γC n).map (fun x => (p ⬝ᵥ zC x, m ⬝ᵥ zC x)) =
      (γC k).map (fun y => (p' ⬝ᵥ zC y, m' ⬝ᵥ zC y)) := by
  have c1 : Continuous fun x : Fin n → ℝ × ℝ => (p ⬝ᵥ zC x, m ⬝ᵥ zC x) :=
    (cont_dotC p).prodMk (cont_dotC m)
  have c2 : Continuous fun x : Fin k → ℝ × ℝ => (p' ⬝ᵥ zC x, m' ⬝ᵥ zC x) :=
    (cont_dotC p').prodMk (cont_dotC m')
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply, integral_map c1.aemeasurable (by fun_prop),
    integral_map c2.aemeasurable (by fun_prop)]
  have e : ∀ {N : ℕ} (a b : Fin N → ℂ) (x : Fin N → ℝ × ℝ),
      L (a ⬝ᵥ zC x, b ⬝ᵥ zC x) =
        (((⟨L (1, 0), -L (I, 0)⟩ : ℂ) • a + (⟨L (0, 1), -L (0, I)⟩ : ℂ) • b) ⬝ᵥ zC x).re := by
    intro N a b x
    rw [dualProdC, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  simp_rw [e, cfC, sumNormSq, h1, h2, h3]

lemma intC {n k : ℕ} (p m : Fin n → ℂ) (p' m' : Fin k → ℂ)
    (h1 : ∑ i, normSq (p i) = ∑ i, normSq (p' i))
    (h2 : p ⬝ᵥ star m = p' ⬝ᵥ star m') (h3 : ∑ i, normSq (m i) = ∑ i, normSq (m' i))
    (f : ℂ × ℂ → ℝ) (hf : Continuous f) :
    ∫ x, f (p ⬝ᵥ zC x, m ⬝ᵥ zC x) ∂γC n = ∫ y, f (p' ⬝ᵥ zC y, m' ⬝ᵥ zC y) ∂γC k := by
  have c1 : Continuous fun x : Fin n → ℝ × ℝ => (p ⬝ᵥ zC x, m ⬝ᵥ zC x) :=
    (cont_dotC p).prodMk (cont_dotC m)
  have c2 : Continuous fun x : Fin k → ℝ × ℝ => (p' ⬝ᵥ zC x, m' ⬝ᵥ zC x) :=
    (cont_dotC p').prodMk (cont_dotC m')
  rw [← integral_map (f := f) c1.aemeasurable hf.aestronglyMeasurable,
    ← integral_map (f := f) c2.aemeasurable hf.aestronglyMeasurable, lawC p m p' m' h1 h2 h3]

end

end S192B412


namespace S192B412

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Real Complex ComplexConjugate

lemma sqIntR : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq

lemma integR {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (C : ℝ)
    (h : ∀ x, |f x| ≤ C * ∑ j, x j ^ 2) : Integrable f (γR n) := by
  refine Integrable.mono' (g := fun x => C * ∑ j, x j ^ 2) ?_ hf.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact h x)
  exact (integrable_finsetSum _ fun j _ =>
    (integrable_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1) (i := j)
      (f := fun t : ℝ => t ^ 2) sqIntR :)).const_mul C

lemma dot_self_nonneg {n : ℕ} (p : Fin n → ℝ) : 0 ≤ p ⬝ᵥ p :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)

lemma intDiag {n : ℕ} (p m : Fin n → ℝ) (hpm : p ⬝ᵥ m = 0) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) :
    ∫ x, f (p ⬝ᵥ x, m ⬝ᵥ x) ∂γR n = ∫ y, f (√(p ⬝ᵥ p) * y 0, √(m ⬝ᵥ m) * y 1) ∂γR 2 := by
  rw [intR p m ![√(p ⬝ᵥ p), 0] ![0, √(m ⬝ᵥ m)] ?_ ?_ ?_ f hf]
  · simp [dotProduct, Fin.sum_univ_two]
  · simpa [dotProduct, Fin.sum_univ_two] using (mul_self_sqrt (dot_self_nonneg p)).symm
  · simpa [dotProduct, Fin.sum_univ_two] using hpm
  · simpa [dotProduct, Fin.sum_univ_two] using (mul_self_sqrt (dot_self_nonneg m)).symm

lemma prodAbsR : ∫ y, |y 0| * |y 1| ∂γR 2 = 2 / π := by
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin 2 => gaussianReal 0 1)
    (fun _ (t : ℝ) => |t|)
  simp only [Fin.prod_univ_two] at this
  rw [this, ← sq, absMomentReal]

lemma diffSqR : ∫ y, |y 0 ^ 2 - y 1 ^ 2| ∂γR 2 = 4 / π := by
  have h := intDiag ![1, -1] ![1, 1] (by simp [dotProduct, Fin.sum_univ_two])
    (fun u => |u.1| * |u.2|) (by fun_prop)
  have e1 : (![1, -1] : Fin 2 → ℝ) ⬝ᵥ ![1, -1] = 2 := by
    simp [dotProduct, Fin.sum_univ_two]; norm_num
  have e2 : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] = 2 := by
    simp [dotProduct, Fin.sum_univ_two]; norm_num
  rw [e1, e2] at h
  have l : ∀ y : Fin 2 → ℝ, |y 0 ^ 2 - y 1 ^ 2| =
      |(![1, -1] : Fin 2 → ℝ) ⬝ᵥ y| * |(![1, 1] : Fin 2 → ℝ) ⬝ᵥ y| := by
    intro y
    simp only [dotProduct, Fin.sum_univ_two]
    rw [← abs_mul]; congr 1; simp; ring
  have r : ∀ y : Fin 2 → ℝ, |√2 * y 0| * |√2 * y 1| = 2 * (|y 0| * |y 1|) := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < √2)]
    have := mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    linear_combination (|y 0| * |y 1|) * this
  simp_rw [l]
  rw [h]
  simp_rw [r]
  rw [integral_const_mul, prodAbsR]
  ring

lemma symR (α β : ℝ) (hab : 0 ≤ α + β) :
    (α + β) / 2 * (4 / π) ≤ ∫ y, |α * y 0 ^ 2 - β * y 1 ^ 2| ∂γR 2 := by
  have sw := intR ![1, 0] ![0, 1] ![0, 1] ![1, 0] (by simp [dotProduct, Fin.sum_univ_two])
    (by simp [dotProduct, Fin.sum_univ_two]) (by simp [dotProduct, Fin.sum_univ_two])
    (fun u => |α * u.1 ^ 2 - β * u.2 ^ 2|) (by fun_prop)
  simp only [dotProduct, Fin.sum_univ_two] at sw
  simp at sw
  have bnd : ∀ (a b : ℝ) (y : Fin 2 → ℝ), |a * y 0 ^ 2 - b * y 1 ^ 2| ≤
      (|a| + |b|) * ∑ j, y j ^ 2 := by
    intro a b y
    simp only [Fin.sum_univ_two]
    calc |a * y 0 ^ 2 - b * y 1 ^ 2| ≤ |a * y 0 ^ 2| + |b * y 1 ^ 2| := abs_sub _ _
      _ = |a| * y 0 ^ 2 + |b| * y 1 ^ 2 := by
          simp only [abs_mul, abs_pow, sq_abs]
      _ ≤ _ := by nlinarith [abs_nonneg a, abs_nonneg b, sq_nonneg (y 0), sq_nonneg (y 1)]
  have i1 := integR (fun y : Fin 2 → ℝ => |α * y 0 ^ 2 - β * y 1 ^ 2|) (by fun_prop) _
    (fun y => by rw [abs_abs]; exact bnd α β y)
  have i2 : Integrable (fun y : Fin 2 → ℝ => |α * y 1 ^ 2 - β * y 0 ^ 2|) (γR 2) := by
    refine integR _ (by fun_prop) (|α| + |β|) fun y => ?_
    simp only [Fin.sum_univ_two, abs_abs]
    calc |α * y 1 ^ 2 - β * y 0 ^ 2| ≤ |α * y 1 ^ 2| + |β * y 0 ^ 2| := abs_sub _ _
      _ = |α| * y 1 ^ 2 + |β| * y 0 ^ 2 := by
          simp only [abs_mul, abs_pow, sq_abs]
      _ ≤ _ := by nlinarith [abs_nonneg α, abs_nonneg β, sq_nonneg (y 0), sq_nonneg (y 1)]
  have key : ∫ y, (α + β) * |y 0 ^ 2 - y 1 ^ 2| ∂γR 2 ≤
      ∫ y, (|α * y 0 ^ 2 - β * y 1 ^ 2| + |α * y 1 ^ 2 - β * y 0 ^ 2|) ∂γR 2 := by
    refine integral_mono ((integR (fun y : Fin 2 → ℝ => |y 0 ^ 2 - y 1 ^ 2|) (by fun_prop) _
      (fun y => by rw [abs_abs]; simpa using bnd 1 1 y)).const_mul _) (i1.add i2) fun y => ?_
    have := abs_sub (α * y 0 ^ 2 - β * y 1 ^ 2) (α * y 1 ^ 2 - β * y 0 ^ 2)
    have e : (α + β) * (y 0 ^ 2 - y 1 ^ 2) =
        α * y 0 ^ 2 - β * y 1 ^ 2 - (α * y 1 ^ 2 - β * y 0 ^ 2) := by ring
    rw [← abs_of_nonneg hab, ← abs_mul, e]
    exact this
  rw [integral_const_mul, diffSqR, integral_add i1 i2, ← sw] at key
  linarith

lemma keyR {n : ℕ} (a b : Fin n → ℝ) :
    2 / π * √(a ⬝ᵥ a) * √(b ⬝ᵥ b) ≤ ∫ x, |a ⬝ᵥ x| * |b ⬝ᵥ x| ∂γR n := by
  set s := √(a ⬝ᵥ a) with hs
  set t := √(b ⬝ᵥ b) with ht
  have s0 : 0 ≤ s := sqrt_nonneg _
  have t0 : 0 ≤ t := sqrt_nonneg _
  rcases s0.eq_or_lt with hs0 | hs0
  · rw [← hs0, mul_zero, zero_mul]
    exact integral_nonneg fun x => by positivity
  rcases t0.eq_or_lt with ht0 | ht0
  · rw [← ht0, mul_zero]
    exact integral_nonneg fun x => by positivity
  have saa : a ⬝ᵥ a = s ^ 2 := by rw [hs, sq_sqrt (dot_self_nonneg a)]
  have tbb : b ⬝ᵥ b = t ^ 2 := by rw [ht, sq_sqrt (dot_self_nonneg b)]
  set p := t • a + s • b with hp
  set m := t • a - s • b with hm
  have dd : ∀ u v : Fin n → ℝ, ∀ c d e f : ℝ, (c • u + d • v) ⬝ᵥ (e • u + f • v) =
      c * e * (u ⬝ᵥ u) + (c * f + d * e) * (u ⬝ᵥ v) + d * f * (v ⬝ᵥ v) := by
    intro u v c d e f
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm v u]
    ring
  have hm' : m = t • a + (-s) • b := by rw [hm, neg_smul, sub_eq_add_neg]
  have hpm : p ⬝ᵥ m = 0 := by
    rw [hm', hp, dd, saa, tbb]; ring
  have hpp : p ⬝ᵥ p = 2 * s ^ 2 * t ^ 2 + 2 * s * t * (a ⬝ᵥ b) := by
    rw [hp, dd, saa, tbb]; ring
  have hmm : m ⬝ᵥ m = 2 * s ^ 2 * t ^ 2 - 2 * s * t * (a ⬝ᵥ b) := by
    rw [hm', dd, saa, tbb]; ring
  have pt : ∀ x, |a ⬝ᵥ x| * |b ⬝ᵥ x| =
      (fun u : ℝ × ℝ => |u.1 + u.2| * |u.1 - u.2| / (4 * s * t)) (p ⬝ᵥ x, m ⬝ᵥ x) := by
    intro x
    simp only [hp, hm, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [show t * (a ⬝ᵥ x) + s * (b ⬝ᵥ x) + (t * (a ⬝ᵥ x) - s * (b ⬝ᵥ x)) = (2 * t) * (a ⬝ᵥ x)
      by ring, show t * (a ⬝ᵥ x) + s * (b ⬝ᵥ x) - (t * (a ⬝ᵥ x) - s * (b ⬝ᵥ x)) =
      (2 * s) * (b ⬝ᵥ x) by ring, abs_mul (2 * t), abs_mul (2 * s), abs_of_pos (by positivity : 0 < 2 * t),
      abs_of_pos (by positivity : 0 < 2 * s)]
    field_simp
    ring
  have hD := intDiag p m hpm (fun u : ℝ × ℝ => |u.1 + u.2| * |u.1 - u.2| / (4 * s * t))
    (by fun_prop)
  simp only at hD pt
  simp_rw [pt]
  rw [hD]
  have pt2 : ∀ y : Fin 2 → ℝ, |√(p ⬝ᵥ p) * y 0 + √(m ⬝ᵥ m) * y 1| *
      |√(p ⬝ᵥ p) * y 0 - √(m ⬝ᵥ m) * y 1| / (4 * s * t) =
      (1 / (4 * s * t)) * |(p ⬝ᵥ p) * y 0 ^ 2 - (m ⬝ᵥ m) * y 1 ^ 2| := by
    intro y
    rw [← abs_mul, ← sq_sqrt (dot_self_nonneg p), ← sq_sqrt (dot_self_nonneg m)]
    rw [sqrt_sq (sqrt_nonneg _), sqrt_sq (sqrt_nonneg _)]
    rw [div_eq_mul_inv, one_div, mul_comm]
    congr 2; ring
  simp_rw [pt2]
  rw [integral_const_mul]
  have := symR (p ⬝ᵥ p) (m ⬝ᵥ m) (by linarith [dot_self_nonneg p, dot_self_nonneg m])
  rw [hpp, hmm] at this ⊢
  calc 2 / π * s * t = 1 / (4 * s * t) * ((2 * s ^ 2 * t ^ 2 + 2 * s * t * (a ⬝ᵥ b) +
      (2 * s ^ 2 * t ^ 2 - 2 * s * t * (a ⬝ᵥ b))) / 2 * (4 / π)) := by
        field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

end

end S192B412


namespace S192B412

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Real Complex ComplexConjugate

lemma outer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p q : ℕ}
    (U : Fin p → Ω → ℝ) (V : Fin q → Ω → ℝ) (hU : ∀ i x, 0 ≤ U i x) (hV : ∀ j x, 0 ≤ V j x)
    (w : Fin p → ℝ) (v : Fin q → ℝ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hint : ∀ i j, Integrable (fun x => U i x * V j x) μ)
    (hU2 : ∀ i, Integrable (fun x => U i x ^ 2) μ) (hV2 : ∀ j, Integrable (fun x => V j x ^ 2) μ)
    (hkey : ∀ i j, κ * w i * v j ≤ ∫ x, U i x * V j x ∂μ)
    (hmeas : AEStronglyMeasurable (fun x => √(∑ i, U i x ^ 2) * √(∑ j, V j x ^ 2)) μ) :
    Integrable (fun x => √(∑ i, U i x ^ 2) * √(∑ j, V j x ^ 2)) μ ∧
      κ * √(∑ i, w i ^ 2) * √(∑ j, v j ^ 2) ≤
        ∫ x, √(∑ i, U i x ^ 2) * √(∑ j, V j x ^ 2) ∂μ := by
  have gnn : ∀ x, 0 ≤ √(∑ i, U i x ^ 2) * √(∑ j, V j x ^ 2) := fun x => by positivity
  have hgint : Integrable (fun x => √(∑ i, U i x ^ 2) * √(∑ j, V j x ^ 2)) μ := by
    refine Integrable.mono' (g := fun x => (∑ i, U i x ^ 2 + ∑ j, V j x ^ 2) / 2)
      (((integrable_finsetSum _ fun i _ => hU2 i).add
        (integrable_finsetSum _ fun j _ => hV2 j)).div_const 2) hmeas
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (gnn x)]
    have a1 : 0 ≤ ∑ i, U i x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have a2 : 0 ≤ ∑ j, V j x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [sq_nonneg (√(∑ i, U i x ^ 2) - √(∑ j, V j x ^ 2)), sq_sqrt a1, sq_sqrt a2]
  refine ⟨hgint, ?_⟩
  set F := √(∑ i, w i ^ 2) with hF
  set G := √(∑ j, v j ^ 2) with hG
  by_cases hF0 : F = 0
  · rw [hF0, mul_zero, zero_mul]; exact integral_nonneg gnn
  by_cases hG0 : G = 0
  · rw [hG0, mul_zero]; exact integral_nonneg gnn
  have hF0 : 0 < F := lt_of_le_of_ne (sqrt_nonneg _) (Ne.symm hF0)
  have hG0 : 0 < G := lt_of_le_of_ne (sqrt_nonneg _) (Ne.symm hG0)
  have pw : ∀ x, ∑ i, ∑ j, (w i * v j / (F * G)) * (U i x * V j x) ≤
      √(∑ i, U i x ^ 2) * √(∑ j, V j x ^ 2) := by
    intro x
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ w (fun i => U i x)
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v (fun j => V j x)
    have e : ∑ i, ∑ j, (w i * v j / (F * G)) * (U i x * V j x) =
        (∑ i, w i * U i x) * (∑ j, v j * V j x) / (F * G) := by
      rw [Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, div_le_iff₀ (by positivity)]
    calc (∑ i, w i * U i x) * (∑ j, v j * V j x) ≤
        (F * √(∑ i, U i x ^ 2)) * (G * √(∑ j, V j x ^ 2)) :=
          mul_le_mul h1 h2 (Finset.sum_nonneg fun j _ => mul_nonneg (hv j) (hV j x))
            (by positivity)
      _ = _ := by ring
  have sF : ∑ i, w i ^ 2 = F ^ 2 := by
    rw [hF, sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have sG : ∑ j, v j ^ 2 = G ^ 2 := by
    rw [hG, sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc κ * F * G = ∑ i, ∑ j, (w i * v j / (F * G)) * (κ * w i * v j) := by
        have : ∑ i, ∑ j, (w i * v j / (F * G)) * (κ * w i * v j) =
            κ / (F * G) * ((∑ i, w i ^ 2) * (∑ j, v j ^ 2)) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [this, sF, sG]
        field_simp
    _ ≤ ∑ i, ∑ j, (w i * v j / (F * G)) * ∫ x, U i x * V j x ∂μ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hkey i j) (div_nonneg (mul_nonneg (hw i) (hv j))
            (by positivity))
    _ = ∫ x, ∑ i, ∑ j, (w i * v j / (F * G)) * (U i x * V j x) ∂μ := by
        rw [integral_finset_sum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hint i j).const_mul _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finset_sum _ fun j _ => (hint i j).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
    _ ≤ _ := integral_mono (integrable_finsetSum _ fun i _ => integrable_finsetSum _
          fun j _ => (hint i j).const_mul _) hgint pw

theorem realPart : ∀ (p q n : ℕ), 0 < p → 0 < q → 0 < n →
      ∀ (L : Matrix (Fin p) (Fin n) ℝ) (R : Matrix (Fin q) (Fin n) ℝ),
        let γ : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1
        let g : (Fin n → ℝ) → ℝ := fun x =>
          Real.sqrt (∑ i, ((L *ᵥ x) i) ^ 2) * Real.sqrt (∑ i, ((R *ᵥ x) i) ^ 2)
        Integrable g γ ∧ (∫ x, g x ∂γ) ≥ (2 / Real.pi) *
          Real.sqrt (∑ i, ∑ j, (L i j) ^ 2) * Real.sqrt (∑ i, ∑ j, (R i j) ^ 2) := by
  intro p q n _ _ _ L R
  dsimp only
  have bnd : ∀ (a : Fin n → ℝ) (x : Fin n → ℝ), (a ⬝ᵥ x) ^ 2 ≤ (a ⬝ᵥ a) * ∑ j, x j ^ 2 := by
    intro a x
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a x
    simpa [dotProduct, sq] using this
  have hint2 : ∀ a : Fin n → ℝ, Integrable (fun x => |a ⬝ᵥ x| ^ 2) (γR n) := fun a =>
    integR _ (by have := cont_dotR a; fun_prop) (a ⬝ᵥ a) fun x => by
      rw [sq_abs, abs_of_nonneg (sq_nonneg _)]; exact bnd a x
  have hint : ∀ a b : Fin n → ℝ, Integrable (fun x => |a ⬝ᵥ x| * |b ⬝ᵥ x|) (γR n) :=
    fun a b => integR _ (by have := cont_dotR a; have := cont_dotR b; fun_prop)
      ((a ⬝ᵥ a + b ⬝ᵥ b) / 2) fun x => by
        rw [abs_of_nonneg (by positivity)]
        have h1 := bnd a x
        have h2 := bnd b x
        nlinarith [sq_nonneg (|a ⬝ᵥ x| - |b ⬝ᵥ x|), sq_abs (a ⬝ᵥ x), sq_abs (b ⬝ᵥ x)]
  have := outer (γR n) (fun i x => |L i ⬝ᵥ x|) (fun j x => |R j ⬝ᵥ x|)
    (fun _ _ => abs_nonneg _) (fun _ _ => abs_nonneg _) (fun i => √(L i ⬝ᵥ L i))
    (fun j => √(R j ⬝ᵥ R j)) (fun _ => sqrt_nonneg _) (fun _ => sqrt_nonneg _) (2 / π)
    (by positivity) (fun i j => hint _ _) (fun i => hint2 _) (fun j => hint2 _)
    (fun i j => keyR _ _) (by
      have := fun i => cont_dotR (L i)
      have := fun j => cont_dotR (R j)
      exact Continuous.aestronglyMeasurable (by fun_prop))
  simp only [sq_abs, sq_sqrt (dot_self_nonneg _)] at this
  simp only [dotProduct, ← sq] at this
  exact this

end

end S192B412


namespace S192B412

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Real Complex ComplexConjugate

lemma sqIntH : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 (1 / 2)) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1 / 2) 2).integrable_sq

lemma integC {n : ℕ} (f : (Fin n → ℝ × ℝ) → ℝ) (hf : Continuous f) (C : ℝ)
    (h : ∀ x, |f x| ≤ C * ∑ j, ‖zC x j‖ ^ 2) : Integrable f (γC n) := by
  have e : ∀ x : Fin n → ℝ × ℝ, ∑ j, ‖zC x j‖ ^ 2 = ∑ j, ((x j).1 ^ 2 + (x j).2 ^ 2) := by
    intro x
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.sq_norm, zC, normSq_mk]; ring
  refine Integrable.mono' (g := fun x => C * ∑ j, ((x j).1 ^ 2 + (x j).2 ^ 2)) ?_
    hf.aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs, ← e]; exact h x)
  refine (integrable_finsetSum _ fun j _ => ?_).const_mul C
  have h1 := sqIntH.comp_fst (gaussianReal 0 (1 / 2))
  have h2 := sqIntH.comp_snd (gaussianReal 0 (1 / 2))
  exact (integrable_comp_eval (μ := fun _ : Fin n => (gaussianReal 0 (1 / 2)).prod
    (gaussianReal 0 (1 / 2))) (i := j) (h1.add h2) :)

lemma normSq_sum_nonneg {n : ℕ} (p : Fin n → ℂ) : 0 ≤ ∑ i, normSq (p i) :=
  Finset.sum_nonneg fun i _ => normSq_nonneg _

lemma bndC {n : ℕ} (a : Fin n → ℂ) (z : Fin n → ℂ) :
    ‖a ⬝ᵥ z‖ ^ 2 ≤ (∑ i, normSq (a i)) * ∑ j, ‖z j‖ ^ 2 := by
  have h1 : ‖a ⬝ᵥ z‖ ≤ ∑ i, ‖a i‖ * ‖z i‖ := by
    simp only [dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖a i‖) (fun i => ‖z i‖)
  simp only [Complex.sq_norm] at h2 ⊢
  rw [← Complex.sq_norm]
  calc ‖a ⬝ᵥ z‖ ^ 2 ≤ (∑ i, ‖a i‖ * ‖z i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by simpa [Complex.sq_norm] using h2

lemma dot_star_self {n : ℕ} (u : Fin n → ℂ) :
    u ⬝ᵥ star u = ((∑ i, normSq (u i) : ℝ) : ℂ) := by
  simp [dotProduct, Complex.mul_conj, ofReal_sum]

lemma intDiagC {n : ℕ} (p m : Fin n → ℂ) (hpm : p ⬝ᵥ star m = 0) (f : ℂ × ℂ → ℝ)
    (hf : Continuous f) :
    ∫ x, f (p ⬝ᵥ zC x, m ⬝ᵥ zC x) ∂γC n =
      ∫ y, f (((√(∑ i, normSq (p i)) : ℝ) : ℂ) * zC y 0,
        ((√(∑ i, normSq (m i)) : ℝ) : ℂ) * zC y 1) ∂γC 2 := by
  rw [intC p m ![((√(∑ i, normSq (p i)) : ℝ) : ℂ), 0] ![0, ((√(∑ i, normSq (m i)) : ℝ) : ℂ)]
    ?_ ?_ ?_ f hf]
  · simp [dotProduct, Fin.sum_univ_two]
  · simp [Fin.sum_univ_two, normSq_ofReal, mul_self_sqrt (normSq_sum_nonneg p)]
  · simpa [dotProduct, Fin.sum_univ_two] using hpm
  · simp [Fin.sum_univ_two, normSq_ofReal, mul_self_sqrt (normSq_sum_nonneg m)]

lemma prodAbsC : ∫ y, ‖zC y 0‖ * ‖zC y 1‖ ∂γC 2 = π / 4 := by
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : Fin 2 => (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)))
    (fun _ (t : ℝ × ℝ) => ‖(⟨t.1, t.2⟩ : ℂ)‖)
  simp only [Fin.prod_univ_two] at this
  simp only [zC]
  rw [this, absMomentComplex]
  have h := mul_self_sqrt pi_pos.le
  linear_combination h / 4

lemma bndUV (a b u v : ℂ) :
    ‖a * u ^ 2 - b * v ^ 2‖ ≤ (‖a‖ + ‖b‖) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  calc ‖a * u ^ 2 - b * v ^ 2‖ ≤ ‖a * u ^ 2‖ + ‖b * v ^ 2‖ := norm_sub_le _ _
    _ = ‖a‖ * ‖u‖ ^ 2 + ‖b‖ * ‖v‖ ^ 2 := by rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ _ := by nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg ‖u‖, sq_nonneg ‖v‖]

lemma bnd2C (a b : ℂ) (y : Fin 2 → ℝ × ℝ) :
    |‖a * zC y 0 ^ 2 - b * zC y 1 ^ 2‖| ≤ (‖a‖ + ‖b‖) * ∑ j, ‖zC y j‖ ^ 2 := by
  rw [abs_of_nonneg (norm_nonneg _), Fin.sum_univ_two]
  calc ‖a * zC y 0 ^ 2 - b * zC y 1 ^ 2‖ ≤ ‖a * zC y 0 ^ 2‖ + ‖b * zC y 1 ^ 2‖ :=
        norm_sub_le _ _
    _ = ‖a‖ * ‖zC y 0‖ ^ 2 + ‖b‖ * ‖zC y 1‖ ^ 2 := by rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ _ := by nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg ‖zC y 0‖, sq_nonneg ‖zC y 1‖]

lemma diffSqC : ∫ y, ‖zC y 0 ^ 2 - zC y 1 ^ 2‖ ∂γC 2 = π / 2 := by
  have h := intDiagC ![1, -1] ![1, 1] (by simp [dotProduct, Fin.sum_univ_two])
    (fun u => ‖u.1‖ * ‖u.2‖) (by fun_prop)
  have e1 : ∑ i, normSq ((![1, -1] : Fin 2 → ℂ) i) = 2 := by
    simp [Fin.sum_univ_two]; norm_num
  have e2 : ∑ i, normSq ((![1, 1] : Fin 2 → ℂ) i) = 2 := by
    simp [Fin.sum_univ_two]; norm_num
  rw [e1, e2] at h
  have l : ∀ y : Fin 2 → ℝ × ℝ, ‖zC y 0 ^ 2 - zC y 1 ^ 2‖ =
      ‖(![1, -1] : Fin 2 → ℂ) ⬝ᵥ zC y‖ * ‖(![1, 1] : Fin 2 → ℂ) ⬝ᵥ zC y‖ := by
    intro y
    simp only [dotProduct, Fin.sum_univ_two]
    rw [← norm_mul]; congr 1; simp; ring
  have r : ∀ y : Fin 2 → ℝ × ℝ, ‖((√2 : ℝ) : ℂ) * zC y 0‖ * ‖((√2 : ℝ) : ℂ) * zC y 1‖ =
      2 * (‖zC y 0‖ * ‖zC y 1‖) := by
    intro y
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < √2)]
    have := mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    linear_combination (‖zC y 0‖ * ‖zC y 1‖) * this
  simp_rw [l]
  rw [h]
  simp_rw [r]
  rw [integral_const_mul, prodAbsC]
  ring

lemma symC (α β : ℝ) (hab : 0 ≤ α + β) :
    (α + β) / 2 * (π / 2) ≤ ∫ y, ‖(α : ℂ) * zC y 0 ^ 2 - (β : ℂ) * zC y 1 ^ 2‖ ∂γC 2 := by
  have sw := intC ![1, 0] ![0, 1] ![0, 1] ![1, 0] (by simp [Fin.sum_univ_two])
    (by simp [dotProduct, Fin.sum_univ_two]) (by simp [Fin.sum_univ_two])
    (fun u => ‖(α : ℂ) * u.1 ^ 2 - (β : ℂ) * u.2 ^ 2‖) (by fun_prop)
  simp only [dotProduct, Fin.sum_univ_two] at sw
  simp at sw
  have i1 := integC (fun y => ‖(α : ℂ) * zC y 0 ^ 2 - (β : ℂ) * zC y 1 ^ 2‖) (by
    have := cont_zC (n := 2); fun_prop) _ (bnd2C _ _)
  have i2 : Integrable (fun y => ‖(α : ℂ) * zC y 1 ^ 2 - (β : ℂ) * zC y 0 ^ 2‖) (γC 2) := by
    refine integC _ (by have := cont_zC (n := 2); fun_prop) (‖(α:ℂ)‖ + ‖(β:ℂ)‖) fun y => ?_
    rw [abs_of_nonneg (norm_nonneg _), Fin.sum_univ_two, add_comm (‖zC y 0‖ ^ 2)]
    exact bndUV _ _ _ _
  have i3 := integC (fun y : Fin 2 → ℝ × ℝ => ‖zC y 0 ^ 2 - zC y 1 ^ 2‖) (by
    have h0 : Continuous fun y : Fin 2 → ℝ × ℝ => zC y 0 := (continuous_apply 0).comp cont_zC
    have h1 : Continuous fun y : Fin 2 → ℝ × ℝ => zC y 1 := (continuous_apply 1).comp cont_zC
    fun_prop) 2 (fun y => by
      rw [abs_of_nonneg (norm_nonneg _), Fin.sum_univ_two]
      have := bndUV 1 1 (zC y 0) (zC y 1)
      simp only [one_mul, norm_one] at this
      linarith)
  have key : ∫ y, (α + β) * ‖zC y 0 ^ 2 - zC y 1 ^ 2‖ ∂γC 2 ≤
      ∫ y, (‖(α : ℂ) * zC y 0 ^ 2 - (β : ℂ) * zC y 1 ^ 2‖ +
        ‖(α : ℂ) * zC y 1 ^ 2 - (β : ℂ) * zC y 0 ^ 2‖) ∂γC 2 := by
    refine integral_mono (i3.const_mul _) (i1.add i2) fun y => ?_
    have := norm_sub_le ((α : ℂ) * zC y 0 ^ 2 - (β : ℂ) * zC y 1 ^ 2)
      ((α : ℂ) * zC y 1 ^ 2 - (β : ℂ) * zC y 0 ^ 2)
    have e : ((α + β : ℝ) : ℂ) * (zC y 0 ^ 2 - zC y 1 ^ 2) =
        (α : ℂ) * zC y 0 ^ 2 - (β : ℂ) * zC y 1 ^ 2 -
          ((α : ℂ) * zC y 1 ^ 2 - (β : ℂ) * zC y 0 ^ 2) := by push_cast; ring
    have e2 : (α + β) * ‖zC y 0 ^ 2 - zC y 1 ^ 2‖ =
        ‖((α + β : ℝ) : ℂ) * (zC y 0 ^ 2 - zC y 1 ^ 2)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hab]
    rw [e2, e]
    exact this
  rw [integral_const_mul, diffSqC, integral_add i1 i2, ← sw] at key
  linarith

lemma ddC {n : ℕ} (u v : Fin n → ℂ) (c d e f : ℂ) :
    (c • u + d • v) ⬝ᵥ star (e • u + f • v) =
      c * conj e * (u ⬝ᵥ star u) + c * conj f * (u ⬝ᵥ star v) +
        d * conj e * (v ⬝ᵥ star u) + d * conj f * (v ⬝ᵥ star v) := by
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, RCLike.star_def]
  ring

lemma keyC' {n : ℕ} (a b : Fin n → ℂ) (hr : (a ⬝ᵥ star b).im = 0) :
    π / 4 * √(∑ i, normSq (a i)) * √(∑ i, normSq (b i)) ≤
      ∫ x, ‖a ⬝ᵥ zC x‖ * ‖b ⬝ᵥ zC x‖ ∂γC n := by
  set s := √(∑ i, normSq (a i)) with hs
  set t := √(∑ i, normSq (b i)) with ht
  by_cases hs0 : s = 0
  · rw [hs0, mul_zero, zero_mul]; exact integral_nonneg fun x => by positivity
  by_cases ht0 : t = 0
  · rw [ht0, mul_zero]; exact integral_nonneg fun x => by positivity
  have hs0 : 0 < s := lt_of_le_of_ne (sqrt_nonneg _) (Ne.symm hs0)
  have ht0 : 0 < t := lt_of_le_of_ne (sqrt_nonneg _) (Ne.symm ht0)
  have saa : a ⬝ᵥ star a = ((s ^ 2 : ℝ) : ℂ) := by
    rw [dot_star_self, hs, sq_sqrt (normSq_sum_nonneg a)]
  have tbb : b ⬝ᵥ star b = ((t ^ 2 : ℝ) : ℂ) := by
    rw [dot_star_self, ht, sq_sqrt (normSq_sum_nonneg b)]
  have hab : a ⬝ᵥ star b = (((a ⬝ᵥ star b).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hr]
  have hba : b ⬝ᵥ star a = (((a ⬝ᵥ star b).re : ℝ) : ℂ) := by
    have : b ⬝ᵥ star a = star (a ⬝ᵥ star b) := by
      simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this, hab]; simp
  set p := (t : ℂ) • a + (s : ℂ) • b with hp
  set m := (t : ℂ) • a - (s : ℂ) • b with hm
  have hm' : m = (t : ℂ) • a + (-(s : ℂ)) • b := by rw [hm, neg_smul, sub_eq_add_neg]
  have hpm : p ⬝ᵥ star m = 0 := by
    rw [hm', hp, ddC, saa, tbb, hab, hba]
    simp only [map_neg, Complex.conj_ofReal]
    push_cast; ring
  have hsum : (∑ i, normSq (p i)) + ∑ i, normSq (m i) = 4 * s ^ 2 * t ^ 2 := by
    have : ((∑ i, normSq (p i) : ℝ) : ℂ) + ((∑ i, normSq (m i) : ℝ) : ℂ) =
        ((4 * s ^ 2 * t ^ 2 : ℝ) : ℂ) := by
      rw [← dot_star_self, ← dot_star_self, hm', hp, ddC, ddC, saa, tbb, hab, hba]
      simp only [map_neg, Complex.conj_ofReal]
      push_cast; ring
    exact_mod_cast this
  have pt : ∀ x, ‖a ⬝ᵥ zC x‖ * ‖b ⬝ᵥ zC x‖ =
      (fun u : ℂ × ℂ => ‖u.1 + u.2‖ * ‖u.1 - u.2‖ / (4 * s * t)) (p ⬝ᵥ zC x, m ⬝ᵥ zC x) := by
    intro x
    simp only [hp, hm, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [show (t : ℂ) * (a ⬝ᵥ zC x) + (s : ℂ) * (b ⬝ᵥ zC x) + ((t : ℂ) * (a ⬝ᵥ zC x) -
      (s : ℂ) * (b ⬝ᵥ zC x)) = ((2 * t : ℝ) : ℂ) * (a ⬝ᵥ zC x) by push_cast; ring,
      show (t : ℂ) * (a ⬝ᵥ zC x) + (s : ℂ) * (b ⬝ᵥ zC x) - ((t : ℂ) * (a ⬝ᵥ zC x) -
      (s : ℂ) * (b ⬝ᵥ zC x)) = ((2 * s : ℝ) : ℂ) * (b ⬝ᵥ zC x) by push_cast; ring,
      norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * t),
      abs_of_pos (by positivity : 0 < 2 * s)]
    field_simp
    ring
  have hD := intDiagC p m hpm (fun u : ℂ × ℂ => ‖u.1 + u.2‖ * ‖u.1 - u.2‖ / (4 * s * t))
    (by fun_prop)
  simp only at hD pt
  simp_rw [pt]
  rw [hD]
  have pt2 : ∀ y : Fin 2 → ℝ × ℝ,
      ‖((√(∑ i, normSq (p i)) : ℝ) : ℂ) * zC y 0 + ((√(∑ i, normSq (m i)) : ℝ) : ℂ) * zC y 1‖ *
      ‖((√(∑ i, normSq (p i)) : ℝ) : ℂ) * zC y 0 - ((√(∑ i, normSq (m i)) : ℝ) : ℂ) * zC y 1‖
        / (4 * s * t) =
      (1 / (4 * s * t)) * ‖((∑ i, normSq (p i) : ℝ) : ℂ) * zC y 0 ^ 2 -
        ((∑ i, normSq (m i) : ℝ) : ℂ) * zC y 1 ^ 2‖ := by
    intro y
    rw [← norm_mul]
    conv_rhs => rw [← sq_sqrt (normSq_sum_nonneg p), ← sq_sqrt (normSq_sum_nonneg m)]
    rw [div_eq_mul_inv, one_div, mul_comm]
    congr 2; push_cast; ring
  simp_rw [pt2]
  rw [integral_const_mul]
  have := symC (∑ i, normSq (p i)) (∑ i, normSq (m i))
    (by linarith [normSq_sum_nonneg p, normSq_sum_nonneg m])
  rw [hsum] at this
  calc π / 4 * s * t = 1 / (4 * s * t) * (4 * s ^ 2 * t ^ 2 / 2 * (π / 2)) := by
        field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

end

end S192B412


namespace S192B412

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Real Complex ComplexConjugate

lemma keyC {n : ℕ} (a b : Fin n → ℂ) :
    π / 4 * √(∑ i, normSq (a i)) * √(∑ i, normSq (b i)) ≤
      ∫ x, ‖a ⬝ᵥ zC x‖ * ‖b ⬝ᵥ zC x‖ ∂γC n := by
  by_cases h0 : a ⬝ᵥ star b = 0
  · exact keyC' a b (by rw [h0]; simp)
  set h := a ⬝ᵥ star b with hh
  have hn : (‖h‖ : ℂ) ≠ 0 := by simpa using h0
  set ω : ℂ := h / (‖h‖ : ℂ) with hω
  have nω : ‖ω‖ = 1 := by
    rw [hω, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (by simpa using h0)
  have hr : (a ⬝ᵥ star (ω • b)).im = 0 := by
    have : a ⬝ᵥ star (ω • b) = ((‖h‖ : ℝ) : ℂ) := by
      rw [star_smul, dotProduct_smul, ← hh, smul_eq_mul, hω, RCLike.star_def, map_div₀,
        Complex.conj_ofReal, div_mul_eq_mul_div, conj_mul']
      field_simp
    rw [this, Complex.ofReal_im]
  have := keyC' a (ω • b) hr
  have e1 : ∑ i, normSq ((ω • b) i) = ∑ i, normSq (b i) := by
    have : normSq ω = 1 := by rw [← Complex.sq_norm, nω, one_pow]
    simp [normSq_mul, this]
  have e2 : ∀ x, ‖(ω • b) ⬝ᵥ zC x‖ = ‖b ⬝ᵥ zC x‖ := by
    intro x; rw [smul_dotProduct, smul_eq_mul, norm_mul, nω, one_mul]
  simp only [e1, e2] at this
  exact this

theorem complexPart : ∀ (p q n : ℕ), 0 < p → 0 < q → 0 < n →
      ∀ (L : Matrix (Fin p) (Fin n) ℂ) (R : Matrix (Fin q) (Fin n) ℂ),
        let γ : Measure (Fin n → ℝ × ℝ) :=
          Measure.pi fun _ => (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))
        let g : (Fin n → ℝ × ℝ) → ℝ := fun x =>
          let z : Fin n → ℂ := fun i => ⟨(x i).1, (x i).2⟩
          Real.sqrt (∑ i, ‖(L *ᵥ z) i‖ ^ 2) * Real.sqrt (∑ i, ‖(R *ᵥ z) i‖ ^ 2)
        Integrable g γ ∧ (∫ x, g x ∂γ) ≥ (Real.pi / 4) *
          Real.sqrt (∑ i, ∑ j, ‖L i j‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖R i j‖ ^ 2) := by
  intro p q n _ _ _ L R
  dsimp only
  have hint2 : ∀ a : Fin n → ℂ, Integrable (fun x => ‖a ⬝ᵥ zC x‖ ^ 2) (γC n) := fun a =>
    integC _ (by have := cont_dotC a; fun_prop) (∑ i, normSq (a i)) fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact bndC a (zC x)
  have hint : ∀ a b : Fin n → ℂ, Integrable (fun x => ‖a ⬝ᵥ zC x‖ * ‖b ⬝ᵥ zC x‖) (γC n) :=
    fun a b => integC _ (by have := cont_dotC a; have := cont_dotC b; fun_prop)
      ((∑ i, normSq (a i) + ∑ i, normSq (b i)) / 2) fun x => by
        rw [abs_of_nonneg (by positivity)]
        have h1 := bndC a (zC x)
        have h2 := bndC b (zC x)
        nlinarith [sq_nonneg (‖a ⬝ᵥ zC x‖ - ‖b ⬝ᵥ zC x‖)]
  have := outer (γC n) (fun i x => ‖L i ⬝ᵥ zC x‖) (fun j x => ‖R j ⬝ᵥ zC x‖)
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    (fun i => √(∑ j, normSq (L i j)))
    (fun i => √(∑ j, normSq (R i j))) (fun _ => sqrt_nonneg _) (fun _ => sqrt_nonneg _) (π / 4)
    (by positivity) (fun i j => hint _ _) (fun i => hint2 _) (fun j => hint2 _)
    (fun i j => keyC _ _) (by
      have := fun i => cont_dotC (L i)
      have := fun j => cont_dotC (R j)
      exact Continuous.aestronglyMeasurable (by fun_prop))
  simp only [sq_sqrt (normSq_sum_nonneg _)] at this
  simp only [Complex.sq_norm] at this ⊢
  exact this

end

end S192B412

open Matrix MeasureTheory ProbabilityTheory

theorem solution :
    (∀ (p q n : ℕ), 0 < p → 0 < q → 0 < n →
      ∀ (L : Matrix (Fin p) (Fin n) ℂ) (R : Matrix (Fin q) (Fin n) ℂ),
        let γ : Measure (Fin n → ℝ × ℝ) :=
          Measure.pi fun _ => (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))
        let g : (Fin n → ℝ × ℝ) → ℝ := fun x =>
          let z : Fin n → ℂ := fun i => ⟨(x i).1, (x i).2⟩
          Real.sqrt (∑ i, ‖(L *ᵥ z) i‖ ^ 2) * Real.sqrt (∑ i, ‖(R *ᵥ z) i‖ ^ 2)
        Integrable g γ ∧ (∫ x, g x ∂γ) ≥ (Real.pi / 4) *
          Real.sqrt (∑ i, ∑ j, ‖L i j‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖R i j‖ ^ 2)) ∧
    (∀ (p q n : ℕ), 0 < p → 0 < q → 0 < n →
      ∀ (L : Matrix (Fin p) (Fin n) ℝ) (R : Matrix (Fin q) (Fin n) ℝ),
        let γ : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1
        let g : (Fin n → ℝ) → ℝ := fun x =>
          Real.sqrt (∑ i, ((L *ᵥ x) i) ^ 2) * Real.sqrt (∑ i, ((R *ᵥ x) i) ^ 2)
        Integrable g γ ∧ (∫ x, g x ∂γ) ≥ (2 / Real.pi) *
          Real.sqrt (∑ i, ∑ j, (L i j) ^ 2) * Real.sqrt (∑ i, ∑ j, (R i j) ^ 2)) :=
  ⟨S192B412.complexPart, S192B412.realPart⟩

