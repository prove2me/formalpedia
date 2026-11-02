-- Prove2me | solution 1 for SpikedWishart.Separated.gaussian_sesquilinear_form_clt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:19:45.126798+00:00
-- url     : https://prove2.me/submissions/7b19968c-2474-4475-9eb6-f21909fe4559

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE

set_option autoImplicit false
set_option linter.all false

open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder
open Filter Topology MeasureTheory Matrix Complex ProbabilityTheory

namespace SpikedWishart.Separated.Lib

-- ===== from ChildStatements.lean =====
section

/-- Q3 (CLT for Gaussian sesquilinear forms; Bai-Yao 2008 Ann. IHP Thm 7.1, Paul 2007 Lemma):
`H` the `r × M` matrix of i.i.d. standard complex Gaussians, `A` deterministic Hermitian with
`-C ≤ A ≤ C` and `s² = (1/M) tr A² ≥ s₀ > 0`; then `(√M/s)((1/M) H A Hᴴ - ((1/M) tr A)·1)`
converges in law to the `r × r` GUE `(Z + Zᴴ)/√2`. -/
def Q3_sesqCLT : Prop :=
  ∀ (r : ℕ) (C s₀ : ℝ), 0 < s₀ → ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    ∀ f : Matrix (Fin r) (Fin r) ℂ → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
    Tendsto (fun n => ∫ X, f (((Real.sqrt (M n) / Real.sqrt (((A n * A n).trace).re / M n) : ℝ) : ℂ) •
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
            ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ)))
        ∂(SpikedWishart.SoftEdge.sampleLaw (M n) r))
      atTop (𝓝 (∫ Z, f ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ))
        ∂(SpikedWishart.SoftEdge.sampleLaw r r)))

end

-- ===== from Q3a.lean =====
section

/-- `stdComplexGaussian` as a pushforward of two independent `N(0,1/2)`. -/
theorem integral_cg (f : ℂ → ℂ) (hf : AEStronglyMeasurable f SpikedWishart.SoftEdge.stdComplexGaussian) :
    ∫ z, f z ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      ∫ p, f ⟨p.1, p.2⟩ ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian at hf ⊢
  exact integral_map (φ := fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable hf

/-- Scalar characteristic function of the standard complex Gaussian. -/
theorem cg_char (a b : ℝ) :
    ∫ z, cexp (((a * z.re + b * z.im : ℝ) : ℂ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      cexp (-(((a ^ 2 + b ^ 2) / 4 : ℝ) : ℂ)) := by
  rw [integral_cg _ (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, cexp (((a * (⟨p.1, p.2⟩ : ℂ).re + b * (⟨p.1, p.2⟩ : ℂ).im : ℝ) : ℂ) * I) =
      cexp (a * p.1 * I) * cexp (b * p.2 * I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => cexp (a * x * I)) (fun y : ℝ => cexp (b * y * I))]
  rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `E exp(i t x²)` for `x ∼ N(0,1/2)`. -/
theorem g_sq_char (t : ℝ) :
    ∫ x, cexp ((t * x ^ 2 : ℝ) * I) ∂(gaussianReal 0 (1 / 2)) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h : ∀ x : ℝ, gaussianPDFReal 0 (1 / 2) x • cexp ((t * x ^ 2 : ℝ) * I) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * cexp (-(1 - t * I) * (x : ℂ) ^ 2) := by
    intro x
    rw [gaussianPDFReal, Complex.real_smul]
    have h2 : (2 * Real.pi * ((1 / 2 : NNReal) : ℝ)) = Real.pi := by push_cast; ring
    have h3 : (-(x - 0) ^ 2 / (2 * ((1 / 2 : NNReal) : ℝ))) = -x ^ 2 := by push_cast; ring
    have h4 : (((-x ^ 2 : ℝ)) : ℂ) + ((t * x ^ 2 : ℝ) : ℂ) * I = -(1 - t * I) * (x : ℂ) ^ 2 := by
      push_cast; ring
    rw [h2, h3, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv, mul_assoc,
      ← Complex.exp_add, h4]
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian_complex (by simp)]

/-- `E exp(i t |z|²) = 1/(1 - i t)` for the standard complex Gaussian. -/
theorem cg_normSq_char (t : ℝ) :
    ∫ z, cexp ((t * Complex.normSq z : ℝ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      1 / (1 - t * I) := by
  rw [integral_cg _ (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, cexp ((t * Complex.normSq (⟨p.1, p.2⟩ : ℂ) : ℝ) * I) =
      cexp ((t * p.1 ^ 2 : ℝ) * I) * cexp ((t * p.2 ^ 2 : ℝ) * I) := by
    intro p
    rw [← Complex.exp_add, Complex.normSq_mk]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => cexp ((t * x ^ 2 : ℝ) * I))
    (fun y : ℝ => cexp ((t * y ^ 2 : ℝ) * I)), g_sq_char]
  have hb : (1 - (t : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc : ((Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ)) ^ 2 = (Real.pi : ℂ) / (1 - t * I) := by
    rw [one_div, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_nat_inv_pow _ (by norm_num)]
  calc ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ) *
        (((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ))
      = (((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2)⁻¹ * ((Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ)) ^ 2 := by
        push_cast; ring
    _ = 1 / (1 - t * I) := by
        rw [hpi, hc]; field_simp

/-- Characteristic function of `|z|² - 1`. -/
theorem cg_phi (t : ℝ) :
    ∫ z, cexp ((t * (Complex.normSq z - 1) : ℝ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      cexp (-(t * I)) / (1 - t * I) := by
  have h : ∀ z : ℂ, cexp ((t * (Complex.normSq z - 1) : ℝ) * I) =
      cexp (-(t * I)) * cexp ((t * Complex.normSq z : ℝ) * I) := by
    intro z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_const_mul, cg_normSq_char]
  ring

/-- Third-order comparison with the Gaussian characteristic function. -/
theorem phi_sub_gauss_le (t : ℝ) (ht : |t| ≤ 1) :
    ‖cexp (-(t * I)) / (1 - t * I) - cexp (-(((t ^ 2 / 2 : ℝ)) : ℂ))‖ ≤ 2 * |t| ^ 3 := by
  have hb : (1 - (t : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have hnb : 1 ≤ ‖(1 - (t : ℂ) * I)‖ := by
    have : (1 - (t : ℂ) * I).re = 1 := by simp
    calc (1 : ℝ) = |(1 - (t : ℂ) * I).re| := by rw [this]; simp
      _ ≤ ‖(1 - (t : ℂ) * I)‖ := Complex.abs_re_le_norm _
  -- e1 : exp(-it) - (1 - it - t²/2)
  have hx1 : ‖(-(t * I) : ℂ)‖ ≤ 1 := by
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact ht
  have e1 := Complex.exp_bound hx1 (n := 3) (by norm_num)
  have hnx1 : ‖(-(t * I) : ℂ)‖ = |t| := by
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnx1] at e1
  have hs1 : ∑ m ∈ Finset.range 3, (-(t * I) : ℂ) ^ m / (m.factorial : ℂ) = 1 - t * I - (t : ℂ) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hs1] at e1
  -- e2 : exp(-t²/2) - (1 - t²/2)
  have hx2 : |(-(t ^ 2 / 2) : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have : t ^ 2 ≤ 1 := by
      have := abs_le.mp ht
      nlinarith
    linarith
  have e2 := Real.exp_bound hx2 (n := 2) (by norm_num)
  have hs2 : ∑ m ∈ Finset.range 2, (-(t ^ 2 / 2) : ℝ) ^ m / (m.factorial : ℝ) = 1 - t ^ 2 / 2 := by
    simp [Finset.sum_range_succ]; ring
  rw [hs2] at e2
  set E1 : ℂ := cexp (-(t * I)) - (1 - t * I - (t : ℂ) ^ 2 / 2) with hE1
  set E2 : ℝ := Real.exp (-(t ^ 2 / 2)) - (1 - t ^ 2 / 2) with hE2
  have key : (1 - (t : ℂ) * I) * (cexp (-(t * I)) / (1 - t * I) - cexp (-(((t ^ 2 / 2 : ℝ)) : ℂ))) =
      E1 - (t : ℂ) ^ 3 * I / 2 - (1 - t * I) * (E2 : ℂ) := by
    rw [hE1, hE2]
    have : cexp (-(((t ^ 2 / 2 : ℝ)) : ℂ)) = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [this]
    field_simp
    push_cast
    ring_nf
    try rw [Complex.I_sq]
    try ring
  have hE1b : ‖E1‖ ≤ |t| ^ 3 * (2 / 9) := by
    have := e1; norm_num [Nat.factorial] at this ⊢; linarith
  have hE2b : |E2| ≤ |t| ^ 3 * (3 / 16) := by
    have h0 := e2
    rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2 / 2)] at h0
    norm_num [Nat.factorial] at h0
    have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have hta : 0 ≤ |t| := abs_nonneg t
    have : (t ^ 2 / 2) ^ 2 ≤ |t| ^ 3 / 4 := by
      rw [ht2]
      have : |t| ^ 4 ≤ |t| ^ 3 := by
        have := pow_le_pow_of_le_one hta ht (show 3 ≤ 4 by norm_num); exact this
      nlinarith
    nlinarith
  have hn1t : ‖(1 - (t : ℂ) * I)‖ ≤ 2 := by
    calc ‖(1 - (t : ℂ) * I)‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_one]; linarith
  have hk : ‖E1 - (t : ℂ) ^ 3 * I / 2 - (1 - t * I) * (E2 : ℂ)‖ ≤ 2 * |t| ^ 3 := by
    have h3 : ‖(t : ℂ) ^ 3 * I / 2‖ = |t| ^ 3 / 2 := by
      rw [norm_div, norm_mul, Complex.norm_I, norm_pow, Complex.norm_real, Real.norm_eq_abs]; norm_num
    have h4 : ‖(1 - (t : ℂ) * I) * (E2 : ℂ)‖ ≤ 2 * (|t| ^ 3 * (3 / 16)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hn1t hE2b (abs_nonneg _) (by norm_num)
    calc ‖E1 - (t : ℂ) ^ 3 * I / 2 - (1 - t * I) * (E2 : ℂ)‖
        ≤ ‖E1‖ + ‖(t : ℂ) ^ 3 * I / 2‖ + ‖(1 - (t : ℂ) * I) * (E2 : ℂ)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 2 * |t| ^ 3 := by rw [h3]; nlinarith [abs_nonneg t, pow_nonneg (abs_nonneg t) 3]
  have := congrArg norm key
  rw [norm_mul] at this
  calc ‖cexp (-(t * I)) / (1 - t * I) - cexp (-(((t ^ 2 / 2 : ℝ)) : ℂ))‖
      ≤ ‖(1 - (t : ℂ) * I)‖ * ‖cexp (-(t * I)) / (1 - t * I) - cexp (-(((t ^ 2 / 2 : ℝ)) : ℂ))‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hnb
    _ ≤ 2 * |t| ^ 3 := by rw [this]; exact hk

/-- Telescoping bound for products of numbers in the unit disc. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hpa : ‖∏ i ∈ s, a i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) ha'
    have hbj : ‖b j‖ ≤ 1 := hb j (Finset.mem_insert_self _ _)
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        (a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [e]
    calc ‖(a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)‖
        ≤ ‖a j - b j‖ * ‖∏ i ∈ s, a i‖ + ‖b j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖a j - b j‖ * 1 + 1 * ∑ i ∈ s, ‖a i - b i‖ := by
          gcongr
          exact ih ha' hb'
      _ = ‖a j - b j‖ + ∑ i ∈ s, ‖a i - b i‖ := by ring

end

-- ===== from Q3b.lean =====
section

/-- Real Frobenius pairing `Re tr(Tᴴ Y)`, written entrywise. -/
noncomputable def pair {α β : Type*} [Fintype α] [Fintype β] (T Y : Matrix α β ℂ) : ℝ :=
  ∑ a, ∑ b, (star (T a b) * Y a b).re

theorem pair_eq_trace {α β : Type*} [Fintype α] [Fintype β] (T Y : Matrix α β ℂ) :
    pair T Y = (trace (Tᴴ * Y)).re := by
  simp only [pair, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]

theorem pair_self {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ) :
    pair T T = ∑ a, ∑ b, ((T a b).re ^ 2 + (T a b).im ^ 2) := by
  simp only [pair]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp [Complex.mul_re]
  ring

theorem eq_zero_of_pair_self {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ)
    (h : pair T T = 0) : T = 0 := by
  rw [pair_self] at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).mp h
  ext a b
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).mp
    (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
  have hr : (T a b).re = 0 := by nlinarith [sq_nonneg (T a b).re, sq_nonneg (T a b).im]
  have hi : (T a b).im = 0 := by nlinarith [sq_nonneg (T a b).re, sq_nonneg (T a b).im]
  exact Complex.ext (by simp [hr]) (by simp [hi])

/-- Characteristic function of the i.i.d. complex Gaussian array. -/
theorem sample_char (M N : ℕ) (τ : Matrix (Fin M) (Fin N) ℂ) :
    ∫ X, cexp ((pair τ (Matrix.of X) : ℂ) * I) ∂SpikedWishart.SoftEdge.sampleLaw M N =
      cexp (-((pair τ τ / 4 : ℝ) : ℂ)) := by
  have h1 : ∀ X : Fin M → Fin N → ℂ, cexp ((pair τ (Matrix.of X) : ℂ) * I) =
      ∏ m, ∏ j, cexp ((((τ m j).re * (X m j).re + (τ m j).im * (X m j).im : ℝ) : ℂ) * I) := by
    intro X
    simp only [pair, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl (fun m _ => Finset.prod_congr rfl (fun j _ => ?_))
    congr 3
    simp [Complex.mul_re]
  simp_rw [h1]
  unfold SpikedWishart.SoftEdge.sampleLaw
  rw [integral_fintype_prod_eq_prod (fun m (x : Fin N → ℂ) =>
    ∏ j, cexp ((((τ m j).re * (x j).re + (τ m j).im * (x j).im : ℝ) : ℂ) * I))]
  have h2 : ∀ m : Fin M, ∫ x : Fin N → ℂ, ∏ j, cexp ((((τ m j).re * (x j).re +
        (τ m j).im * (x j).im : ℝ) : ℂ) * I) ∂(Measure.pi fun _ => SpikedWishart.SoftEdge.stdComplexGaussian) =
      ∏ j, cexp (-((((τ m j).re ^ 2 + (τ m j).im ^ 2) / 4 : ℝ) : ℂ)) := by
    intro m
    rw [integral_fintype_prod_eq_prod (fun j (z : ℂ) =>
      cexp ((((τ m j).re * z.re + (τ m j).im * z.im : ℝ) : ℂ) * I))]
    exact Finset.prod_congr rfl (fun j _ => cg_char _ _)
  simp_rw [h2]
  rw [pair_self]
  simp only [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The pairing as an `ℝ`-bilinear map on arrays. -/
noncomputable def Lpair (M N : ℕ) :
    (Fin M → Fin N → ℂ) →ₗ[ℝ] (Fin M → Fin N → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => pair (Matrix.of w) (Matrix.of v))
    (fun v1 v2 w => by
      simp only [pair, Matrix.of_apply, Pi.add_apply, mul_add, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r v w => by
      simp only [pair, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Complex.real_smul]; simp [Complex.mul_re]; ring)
    (fun v w1 w2 => by
      simp only [pair, Matrix.of_apply, Pi.add_apply, star_add, add_mul, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r v w => by
      simp only [pair, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Complex.real_smul]; simp [Complex.mul_re]; ring)

theorem Lpair_apply (M N : ℕ) (v w : Fin M → Fin N → ℂ) :
    Lpair M N v w = pair (Matrix.of w) (Matrix.of v) := rfl

theorem continuous_Lpair (M N : ℕ) :
    Continuous fun p : (Fin M → Fin N → ℂ) × (Fin M → Fin N → ℂ) => Lpair M N p.1 p.2 := by
  simp only [Lpair_apply, pair, Matrix.of_apply]
  fun_prop

theorem continuous_pair_of {M N : ℕ} (T : Matrix (Fin M) (Fin N) ℂ) :
    Continuous (fun X : Fin M → Fin N → ℂ => pair T (Matrix.of X)) := by
  simp only [pair, Matrix.of_apply]
  fun_prop

theorem continuous_char_pair {M N : ℕ} (T : Matrix (Fin M) (Fin N) ℂ) :
    Continuous (fun X : Fin M → Fin N → ℂ => cexp ((pair T (Matrix.of X) : ℂ) * I)) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_pair_of T)).mul
    continuous_const)

theorem conjTranspose_map_star {α β : Type*} (Q : Matrix α β ℂ) : (Q.map star)ᴴ = Qᵀ := by
  ext i j; simp

theorem transpose_mul_map_star {α : Type*} [Fintype α] [DecidableEq α] (Q : Matrix α α ℂ)
    (hQ : Q ∈ unitaryGroup α ℂ) : Qᵀ * Q.map star = 1 := by
  have h := mem_unitaryGroup_iff'.mp hQ
  ext i j
  have := congrArg star (congrFun (congrFun h i) j)
  simp only [mul_apply, star_apply, Matrix.one_apply, transpose_apply, map_apply, star_sum,
    star_mul', star_star] at this ⊢
  rw [this]
  split_ifs <;> simp

theorem map_star_mul_transpose {α : Type*} [Fintype α] [DecidableEq α] (P : Matrix α α ℂ)
    (hP : P ∈ unitaryGroup α ℂ) : P.map star * Pᵀ = 1 := by
  have h := mem_unitaryGroup_iff.mp hP
  ext i j
  have := congrArg star (congrFun (congrFun h i) j)
  simp only [mul_apply, star_apply, Matrix.one_apply, transpose_apply, map_apply, star_sum,
    star_mul', star_star] at this ⊢
  rw [this]
  split_ifs <;> simp

/-- Moving a two-sided unitary action across the pairing. -/
theorem pair_unitary {M N : ℕ} (W Y : Matrix (Fin M) (Fin N) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (Q : Matrix (Fin M) (Fin M) ℂ) :
    pair W ((P * Yᵀ * Q)ᵀ) = pair (Q.map star * W * P.map star) Y := by
  rw [pair_eq_trace, pair_eq_trace]
  congr 1
  rw [transpose_mul, transpose_mul, transpose_transpose, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_map_star, conjTranspose_map_star]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

theorem pair_unitary_self {M N : ℕ} (W : Matrix (Fin M) (Fin N) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (Q : Matrix (Fin M) (Fin M) ℂ) (hP : P ∈ unitaryGroup (Fin N) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin M) ℂ) :
    pair (Q.map star * W * P.map star) (Q.map star * W * P.map star) = pair W W := by
  rw [pair_eq_trace, pair_eq_trace]
  congr 1
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_map_star, conjTranspose_map_star]
  have e : Pᵀ * (Wᴴ * Qᵀ) * (Q.map star * W * P.map star) =
      Pᵀ * (Wᴴ * (Qᵀ * Q.map star) * W) * P.map star := by
    simp only [Matrix.mul_assoc]
  rw [e, transpose_mul_map_star Q hQ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    map_star_mul_transpose P hP, Matrix.one_mul]

/-- Unitary invariance of the i.i.d. complex Gaussian array under `H ↦ P H Q`
(`H = (of X)ᵀ`). -/
theorem sample_invariant (M N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ) (Q : Matrix (Fin M) (Fin M) ℂ)
    (hP : P ∈ unitaryGroup (Fin N) ℂ) (hQ : Q ∈ unitaryGroup (Fin M) ℂ) :
    (SpikedWishart.SoftEdge.sampleLaw M N).map
        (fun X => fun m j => (P * (Matrix.of X)ᵀ * Q) j m) =
      SpikedWishart.SoftEdge.sampleLaw M N := by
  have hmeas : Measurable (fun X : Fin M → Fin N → ℂ => fun m j => (P * (Matrix.of X)ᵀ * Q) j m) := by
    apply Continuous.measurable
    simp only [mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have : IsProbabilityMeasure ((SpikedWishart.SoftEdge.sampleLaw M N).map
      (fun X => fun m j => (P * (Matrix.of X)ᵀ * Q) j m)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine ext_of_integral_char_eq Real.continuous_probChar Real.probChar_ne_one
    (L := Lpair M N) ?_ (continuous_Lpair M N) ?_
  · intro v hv h0
    apply hv
    have : Lpair M N v v = 0 := by rw [h0]; rfl
    rw [Lpair_apply] at this
    have := eq_zero_of_pair_self _ this
    funext m j
    exact congrFun (congrFun this m) j
  · intro w
    simp only [BoundedContinuousFunction.char_apply, Real.probChar_apply, Lpair_apply]
    rw [integral_map hmeas.aemeasurable (continuous_char_pair _).aestronglyMeasurable]
    have h3 : ∀ X : Fin M → Fin N → ℂ,
        pair (Matrix.of w) (Matrix.of (fun m j => (P * (Matrix.of X)ᵀ * Q) j m)) =
          pair (Q.map star * Matrix.of w * P.map star) (Matrix.of X) := by
      intro X
      rw [← pair_unitary]
      rfl
    simp_rw [h3]
    rw [sample_char, sample_char, pair_unitary_self _ _ _ hP hQ]

end

-- ===== from Q3c.lean =====
section

theorem herm_decomp {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

/-- The key algebraic identity: `tr(B H A Hᴴ) = Σ_j Σ_m λ_j d_m |G_jm|²` with `G = Wᴴ H V`. -/
theorem trace_BHAH {r M : ℕ} {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian)
    {B : Matrix (Fin r) (Fin r) ℂ} (hB : B.IsHermitian) (H : Matrix (Fin r) (Fin M) ℂ) :
    trace (B * (H * A * Hᴴ)) =
      ∑ m, ∑ j, ((hB.eigenvalues j * hA.eigenvalues m *
        Complex.normSq ((star (hB.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) * H *
          (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)) j m) : ℝ) : ℂ) := by
  set V : Matrix (Fin M) (Fin M) ℂ := (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)
  set W : Matrix (Fin r) (Fin r) ℂ := (hB.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ)
  set G : Matrix (Fin r) (Fin M) ℂ := star W * H * V with hG
  have hA' := herm_decomp hA
  have hB' := herm_decomp hB
  have e : B * (H * A * Hᴴ) =
      W * (diagonal (fun j => ((hB.eigenvalues j : ℝ) : ℂ)) * G *
        diagonal (fun m => ((hA.eigenvalues m : ℝ) : ℂ)) * Gᴴ) * star W := by
    conv_lhs => rw [hA', hB']
    have hWW : W * Wᴴ = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
    rw [hG, conjTranspose_mul, conjTranspose_mul]
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc, hWW,
      Matrix.mul_one]
    rfl
  have hW : star W * W = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  rw [e, Matrix.trace_mul_cycle, hW, Matrix.one_mul]
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.ofReal_mul, diagonal_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

/-- Characteristic function of the centred sesquilinear form `c(H A Hᴴ - tr A)` tested against a
Hermitian `B`, in product form. -/
theorem charT {r M : ℕ} {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian)
    {B : Matrix (Fin r) (Fin r) ℂ} (hB : B.IsHermitian) (c : ℝ) :
    ∫ X, cexp (((trace (B * ((c : ℂ) • ((Matrix.of X)ᵀ * A * ((Matrix.of X)ᵀ)ᴴ) -
        ((c : ℂ) * A.trace) • (1 : Matrix (Fin r) (Fin r) ℂ)))).re : ℂ) * I)
        ∂SpikedWishart.SoftEdge.sampleLaw M r =
      ∏ m, ∏ j, (cexp (-(((c * hB.eigenvalues j * hA.eigenvalues m : ℝ) : ℂ) * I)) /
        (1 - ((c * hB.eigenvalues j * hA.eigenvalues m : ℝ) : ℂ) * I)) := by
  set τ : Fin M → Fin r → ℝ := fun m j => c * hB.eigenvalues j * hA.eigenvalues m with hτ
  set F : (Fin M → Fin r → ℂ) → ℂ :=
    fun Y => cexp (((∑ m, ∑ j, τ m j * (Complex.normSq (Y m j) - 1) : ℝ) : ℂ) * I) with hF
  have hPV : star (hB.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) ∈ unitaryGroup (Fin r) ℂ := Unitary.star_mem hB.eigenvectorUnitary.2
  have hQV : (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ) ∈ unitaryGroup (Fin M) ℂ := hA.eigenvectorUnitary.2
  have htrA : A.trace = ∑ m, ((hA.eigenvalues m : ℝ) : ℂ) := hA.trace_eq_sum_eigenvalues
  have htrB : B.trace = ∑ j, ((hB.eigenvalues j : ℝ) : ℂ) := hB.trace_eq_sum_eigenvalues
  have h1 : ∀ X : Fin M → Fin r → ℂ,
      cexp (((trace (B * ((c : ℂ) • ((Matrix.of X)ᵀ * A * ((Matrix.of X)ᵀ)ᴴ) -
        ((c : ℂ) * A.trace) • (1 : Matrix (Fin r) (Fin r) ℂ)))).re : ℂ) * I) =
      F (fun m j => (star (hB.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) * (Matrix.of X)ᵀ * (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)) j m) := by
    intro X
    rw [hF]
    congr 3
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul,
      trace_smul, trace_BHAH hA hB, htrA, htrB]
    simp only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_sum, Complex.im_sum, zero_mul, sub_zero, mul_zero, Finset.mul_sum, Finset.sum_mul]
    have hS2 : ∑ x : Fin r, ∑ x_1 : Fin M, c * hA.eigenvalues x_1 * hB.eigenvalues x =
        ∑ m : Fin M, ∑ j : Fin r, τ m j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun j _ => ?_))
      simp only [hτ]; ring
    rw [hS2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hτ]
    ring
  simp_rw [h1]
  have hmeas : Measurable (fun X : Fin M → Fin r → ℂ => fun m j => (star (hB.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) * (Matrix.of X)ᵀ * (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)) j m) := by
    apply Continuous.measurable
    simp only [mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have hFc : Continuous F := by
    rw [hF]
    apply Complex.continuous_exp.comp
    apply Continuous.mul _ continuous_const
    apply Complex.continuous_ofReal.comp
    simp only [Complex.normSq_apply]
    fun_prop
  rw [← integral_map hmeas.aemeasurable hFc.aestronglyMeasurable,
    sample_invariant M r _ _ hPV hQV]
  have h2 : ∀ Y : Fin M → Fin r → ℂ, F Y =
      ∏ m, ∏ j, cexp (((τ m j * (Complex.normSq (Y m j) - 1) : ℝ) : ℂ) * I) := by
    intro Y
    rw [hF]
    simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [h2]
  unfold SpikedWishart.SoftEdge.sampleLaw
  rw [integral_fintype_prod_eq_prod (fun m (x : Fin r → ℂ) =>
    ∏ j, cexp (((τ m j * (Complex.normSq (x j) - 1) : ℝ) : ℂ) * I))]
  refine Finset.prod_congr rfl (fun m _ => ?_)
  rw [integral_fintype_prod_eq_prod (fun j (z : ℂ) =>
    cexp (((τ m j * (Complex.normSq z - 1) : ℝ) : ℂ) * I))]
  exact Finset.prod_congr rfl (fun j _ => cg_phi _)

end

-- ===== from Q3d.lean =====
section

/-- `Σ_{a,b} |B_ab|² = Σ_j λ_j²` for Hermitian `B`. -/
theorem pair_herm_eq_sum_sq {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℂ}
    (hB : B.IsHermitian) : pair B B = ∑ j, hB.eigenvalues j ^ 2 := by
  rw [pair_eq_trace, hB.eq]
  set W : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ)
  have hW : star W * W = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hB' := herm_decomp hB
  have e : B * B = W * (diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) *
      diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ))) * star W := by
    conv_lhs => rw [hB']
    have : W * diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) * star W *
        (W * diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) * star W) =
        W * diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) * (star W * W) *
          diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) * star W := by
      simp only [Matrix.mul_assoc]
    rw [this, hW, Matrix.mul_one, Matrix.mul_assoc W]
  rw [e, Matrix.trace_mul_cycle, hW, Matrix.one_mul, diagonal_mul_diagonal, trace_diagonal,
    Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- Characteristic function of the GUE matrix `(Z + Zᴴ)/√2` against a Hermitian `B`. -/
theorem gue_char (r : ℕ) {B : Matrix (Fin r) (Fin r) ℂ} (hB : B.IsHermitian) :
    ∫ Z, cexp (((trace (B * ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)))).re : ℂ) * I)
        ∂SpikedWishart.SoftEdge.sampleLaw r r = cexp (-((pair B B / 2 : ℝ) : ℂ)) := by
  have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have h1 : ∀ Z : Fin r → Fin r → ℂ,
      (trace (B * ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)))).re =
        pair (((Real.sqrt 2 : ℝ) : ℂ) • B) (Matrix.of Z) := by
    intro Z
    rw [pair_eq_trace, conjTranspose_smul, hB.eq, Matrix.mul_smul, Matrix.mul_add, trace_smul,
      trace_add, Matrix.smul_mul, trace_smul]
    have h2 : (trace (B * (Matrix.of Z)ᴴ)) = star (trace (B * Matrix.of Z)) := by
      rw [← trace_conjTranspose, conjTranspose_mul, hB.eq, Matrix.trace_mul_comm]
    rw [h2]
    simp only [smul_eq_mul, Complex.mul_re, Complex.add_re, Complex.star_def, Complex.conj_re,
      Complex.add_im, Complex.conj_im, Complex.inv_re, Complex.inv_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.normSq_ofReal, star_trivial, RCLike.star_def, Complex.conj_ofReal]
    field_simp
    rw [hs]
    ring
  simp_rw [h1]
  rw [sample_char]
  congr 2
  have h3 : pair (((Real.sqrt 2 : ℝ) : ℂ) • B) (((Real.sqrt 2 : ℝ) : ℂ) • B) = 2 * pair B B := by
    simp only [pair, Matrix.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    have : star ((Real.sqrt 2 : ℝ) : ℂ) * star (B a b) * (((Real.sqrt 2 : ℝ) : ℂ) * B a b) =
        ((Real.sqrt 2 ^ 2 : ℝ) : ℂ) * (star (B a b) * B a b) := by
      simp only [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [this, hs, Complex.re_ofReal_mul]
  rw [h3]
  push_cast
  ring

/-- Eigenvalues of `A` with `-C ≤ A ≤ C` lie in `[-C, C]`. -/
theorem abs_eig_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (C : ℝ) (hC : ((C : ℂ) • (1 : Matrix n n ℂ) - A).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix n n ℂ) + A).PosSemidef) (m : n) : |hA.eigenvalues m| ≤ C := by
  set v : n → ℂ := ⇑(hA.eigenvectorBasis m)
  have hv : star v ⬝ᵥ v = 1 := by
    have h := hA.eigenvectorBasis.orthonormal.1 m
    have h2 : (inner ℂ (hA.eigenvectorBasis m) (hA.eigenvectorBasis m)) = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, h]; simp
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
    rw [dotProduct_comm]; exact h2
  have he := hA.eigenvalues_eq m
  have h1 := hC.1.re_dotProduct_nonneg v
  have h2 := hC.2.re_dotProduct_nonneg v
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, hv] at h1
  rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul, hv] at h2
  simp only [smul_eq_mul, mul_one, RCLike.re_to_complex, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re] at h1 h2
  rw [RCLike.re_to_complex] at he
  rw [abs_le]
  constructor <;> linarith

end

-- ===== from Q3e.lean =====
section

theorem norm_phi_le_one (t : ℝ) : ‖cexp (-((t : ℂ) * I)) / (1 - (t : ℂ) * I)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_exp]
  have h0 : (-((t : ℂ) * I)).re = 0 := by simp
  rw [h0, Real.exp_zero]
  have hnb : 1 ≤ ‖(1 - (t : ℂ) * I)‖ := by
    have : (1 - (t : ℂ) * I).re = 1 := by simp
    calc (1 : ℝ) = |(1 - (t : ℂ) * I).re| := by rw [this]; simp
      _ ≤ ‖(1 - (t : ℂ) * I)‖ := Complex.abs_re_le_norm _
  exact (div_le_one (by linarith)).mpr hnb

theorem norm_gauss_le_one (t : ℝ) : ‖cexp (-(((t ^ 2 / 2 : ℝ)) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have h0 : (-(((t ^ 2 / 2 : ℝ)) : ℂ)).re = -(t ^ 2 / 2) := by
    rw [Complex.neg_re, Complex.ofReal_re]
  rw [h0, Real.exp_le_one_iff]
  have := sq_nonneg t
  linarith

/-- Triangular-array product of `phi` converges to the Gaussian characteristic value. -/
theorem prod_phi_tendsto {r : ℕ} (M : ℕ → ℕ) (τ : ∀ n, Fin (M n) → Fin r → ℝ) (S : ℝ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hτ : ∀ n m j, |τ n m j| ≤ δ n)
    (hS : ∀ n, ∑ m, ∑ j, τ n m j ^ 2 = S) :
    Tendsto (fun n => ∏ m, ∏ j, (cexp (-(((τ n m j : ℝ) : ℂ) * I)) /
        (1 - ((τ n m j : ℝ) : ℂ) * I))) atTop (𝓝 (cexp (-((S / 2 : ℝ) : ℂ)))) := by
  have hG : ∀ n, ∏ m, ∏ j, cexp (-(((τ n m j ^ 2 / 2 : ℝ)) : ℂ)) = cexp (-((S / 2 : ℝ) : ℂ)) := by
    intro n
    rw [← hS n]
    simp only [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  have hS0 : 0 ≤ S := by rw [← hS 0]; positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hev : ∀ᶠ n in atTop, δ n ≤ 1 := hδ.eventually (ge_mem_nhds (by norm_num))
  have hbound : ∀ᶠ n in atTop, ‖∏ m, ∏ j, (cexp (-(((τ n m j : ℝ) : ℂ) * I)) /
        (1 - ((τ n m j : ℝ) : ℂ) * I)) - cexp (-((S / 2 : ℝ) : ℂ))‖ ≤ 2 * δ n * S := by
    filter_upwards [hev] with n hn
    rw [← hG n]
    have e1 : ∏ m, ∏ j, (cexp (-(((τ n m j : ℝ) : ℂ) * I)) / (1 - ((τ n m j : ℝ) : ℂ) * I)) =
        ∏ p : Fin (M n) × Fin r, (cexp (-(((τ n p.1 p.2 : ℝ) : ℂ) * I)) /
          (1 - ((τ n p.1 p.2 : ℝ) : ℂ) * I)) := (Fintype.prod_prod_type' _).symm
    have e2 : ∏ m, ∏ j, cexp (-(((τ n m j ^ 2 / 2 : ℝ)) : ℂ)) =
        ∏ p : Fin (M n) × Fin r, cexp (-(((τ n p.1 p.2 ^ 2 / 2 : ℝ)) : ℂ)) :=
      (Fintype.prod_prod_type' _).symm
    rw [e1, e2]
    refine (norm_prod_sub_prod_le _ _ _ (fun i _ => norm_phi_le_one _)
      (fun i _ => norm_gauss_le_one _)).trans ?_
    have e3 : S = ∑ p : Fin (M n) × Fin r, τ n p.1 p.2 ^ 2 := by
      rw [← hS n]; exact (Fintype.sum_prod_type' _).symm
    rw [e3, Finset.mul_sum]
    refine Finset.sum_le_sum (fun p _ => ?_)
    have h1 : |τ n p.1 p.2| ≤ 1 := (hτ n p.1 p.2).trans hn
    refine (phi_sub_gauss_le _ h1).trans ?_
    have h2 : |τ n p.1 p.2| ^ 3 = |τ n p.1 p.2| * τ n p.1 p.2 ^ 2 := by
      rw [← sq_abs (τ n p.1 p.2)]; ring
    rw [h2]
    have := hτ n p.1 p.2
    have h3 : 0 ≤ τ n p.1 p.2 ^ 2 := sq_nonneg _
    nlinarith
  have hlim : Tendsto (fun n => 2 * δ n * S) atTop (𝓝 0) := by
    have := (hδ.const_mul 2).mul_const S
    simpa using this
  exact squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) hbound hlim

end

-- ===== from Q3f.lean =====
section

universe u

/-- Realification of square complex matrices into a Euclidean space. -/
noncomputable def realify (r : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r)) :=
  WithLp.toLp 2 (Sum.elim (fun q => (Y q.1 q.2).re) (fun q => (Y q.1 q.2).im))

/-- Inverse of `realify`. -/
noncomputable def unrealify (r : ℕ) (y : EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => ((WithLp.ofLp y (Sum.inl (a, b)) : ℝ) : ℂ) +
    ((WithLp.ofLp y (Sum.inr (a, b)) : ℝ) : ℂ) * I

theorem unrealify_realify (r : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ) : unrealify r (realify r Y) = Y := by
  ext a b
  simp [unrealify, realify, Complex.re_add_im]

theorem continuous_realify (r : ℕ) : Continuous (realify r) := by
  unfold realify
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  cases p with
  | inl q => simp only [Sum.elim_inl]; fun_prop
  | inr q => simp only [Sum.elim_inr]; fun_prop

theorem continuous_unrealify (r : ℕ) : Continuous (unrealify r) := by
  unfold unrealify
  apply continuous_pi; intro a; apply continuous_pi; intro b
  simp only [Matrix.of_apply]
  have h1 : Continuous fun y : EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r)) =>
      WithLp.ofLp y (Sum.inl (a, b)) :=
    (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)
  have h2 : Continuous fun y : EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r)) =>
      WithLp.ofLp y (Sum.inr (a, b)) :=
    (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)
  fun_prop

theorem inner_realify (r : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (t : EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))) :
    inner ℝ (realify r Y) t = pair (unrealify r t) Y := by
  simp only [realify, unrealify, pair, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, Matrix.of_apply,
    WithLp.ofLp_toLp]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [Complex.mul_re]

/-- Hermitian part of a matrix. -/
noncomputable def hermPart {n : Type*} (τ : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (τᴴ + τ)

theorem hermPart_isHermitian {n : Type*} (τ : Matrix n n ℂ) : (hermPart τ).IsHermitian := by
  unfold hermPart IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem herm_pair {n : Type*} [Fintype n] (τ Y : Matrix n n ℂ) (hY : Y.IsHermitian) :
    pair τ Y = (trace (hermPart τ * Y)).re := by
  have h : trace (τᴴ * Y) = star (trace (τ * Y)) := by
    rw [← trace_conjTranspose, conjTranspose_mul, hY.eq, Matrix.trace_mul_comm]
  rw [pair_eq_trace, hermPart, Matrix.smul_mul, Matrix.add_mul, trace_smul, trace_add, h]
  simp [Complex.mul_re]
  ring

/-- Lévy continuity for random Hermitian matrices, tested by `Re tr(B ·)` with Hermitian `B`. -/
theorem levy_matrix {r : ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ₀ : Measure Ω₀)
    [IsProbabilityMeasure μ₀] (T : ∀ n, Ω n → Matrix (Fin r) (Fin r) ℂ)
    (hT : ∀ n, Measurable (fun ω => realify r (T n ω))) (hTh : ∀ n ω, (T n ω).IsHermitian)
    (T₀ : Ω₀ → Matrix (Fin r) (Fin r) ℂ) (hT₀ : Measurable (fun ω => realify r (T₀ ω)))
    (hT₀h : ∀ ω, (T₀ ω).IsHermitian)
    (hchar : ∀ B : Matrix (Fin r) (Fin r) ℂ, B.IsHermitian →
      Tendsto (fun n => ∫ ω, cexp (((trace (B * T n ω)).re : ℂ) * I) ∂μ n) atTop
        (𝓝 (∫ ω, cexp (((trace (B * T₀ ω)).re : ℂ) * I) ∂μ₀)))
    (f : Matrix (Fin r) (Fin r) ℂ → ℝ) (hf : Continuous f) (hfB : ∃ K, ∀ X, |f X| ≤ K) :
    Tendsto (fun n => ∫ ω, f (T n ω) ∂μ n) atTop (𝓝 (∫ ω, f (T₀ ω) ∂μ₀)) := by
  let ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))) :=
    fun n => ⟨(μ n).map (fun ω => realify r (T n ω)), Measure.isProbabilityMeasure_map (hT n).aemeasurable⟩
  let ν₀ : ProbabilityMeasure (EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))) :=
    ⟨μ₀.map (fun ω => realify r (T₀ ω)), Measure.isProbabilityMeasure_map hT₀.aemeasurable⟩
  have hcont : ∀ t : EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r)),
      Continuous (fun x : EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r)) =>
        cexp ((inner ℝ x t : ℂ) * I)) := by
    intro t
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_id.inner continuous_const)).mul continuous_const)
  have key : ∀ {Ω' : Type u} [MeasurableSpace Ω'] (μ' : Measure Ω') (T' : Ω' → Matrix (Fin r) (Fin r) ℂ),
      Measurable (fun ω => realify r (T' ω)) → (∀ ω, (T' ω).IsHermitian) →
      ∀ t, charFun (μ'.map (fun ω => realify r (T' ω))) t =
        ∫ ω, cexp (((trace (hermPart (unrealify r t) * T' ω)).re : ℂ) * I) ∂μ' := by
    intro Ω' _ μ' T' hm hh t
    rw [charFun_apply, integral_map hm.aemeasurable (hcont t).aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall (fun ω => ?_))
    simp only
    rw [inner_realify, herm_pair _ _ (hh ω)]
  have hc : ∀ t, Tendsto (fun n => charFun ((ν n : Measure (EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))))) t) atTop
      (𝓝 (charFun (ν₀ : Measure (EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r)))) t)) := by
    intro t
    have e1 : ∀ n, charFun ((ν n : Measure (EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))))) t =
        ∫ ω, cexp (((trace (hermPart (unrealify r t) * T n ω)).re : ℂ) * I) ∂μ n :=
      fun n => key (μ n) (T n) (hT n) (hTh n) t
    have e0 : charFun ((ν₀ : Measure (EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))))) t =
        ∫ ω, cexp (((trace (hermPart (unrealify r t) * T₀ ω)).re : ℂ) * I) ∂μ₀ :=
      key μ₀ T₀ hT₀ hT₀h t
    simp_rw [e1, e0]
    exact hchar _ (hermPart_isHermitian _)
  have hconv := ProbabilityMeasure.tendsto_of_tendsto_charFun hc
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv
  obtain ⟨K, hK⟩ := hfB
  have := hconv (BoundedContinuousFunction.ofNormedAddCommGroup (fun y => f (unrealify r y))
    (hf.comp (continuous_unrealify r)) K (fun y => by rw [Real.norm_eq_abs]; exact hK _))
  have hFc : Continuous (fun y : EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r)) =>
      f (unrealify r y)) := hf.comp (continuous_unrealify r)
  have e2 : ∀ n, ∫ ω, (BoundedContinuousFunction.ofNormedAddCommGroup (fun y => f (unrealify r y))
      (hf.comp (continuous_unrealify r)) K (fun y => by rw [Real.norm_eq_abs]; exact hK _)) ω
        ∂((ν n : Measure (EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))))) = ∫ ω, f (T n ω) ∂μ n := by
    intro n
    change ∫ y, f (unrealify r y) ∂((μ n).map (fun ω => realify r (T n ω))) = _
    rw [integral_map (hT n).aemeasurable hFc.aestronglyMeasurable]
    simp only [unrealify_realify]
  have e3 : ∫ ω, (BoundedContinuousFunction.ofNormedAddCommGroup (fun y => f (unrealify r y))
      (hf.comp (continuous_unrealify r)) K (fun y => by rw [Real.norm_eq_abs]; exact hK _)) ω
        ∂((ν₀ : Measure (EuclideanSpace ℝ ((Fin r × Fin r) ⊕ (Fin r × Fin r))))) = ∫ ω, f (T₀ ω) ∂μ₀ := by
    change ∫ y, f (unrealify r y) ∂(μ₀.map (fun ω => realify r (T₀ ω))) = _
    rw [integral_map hT₀.aemeasurable hFc.aestronglyMeasurable]
    simp only [unrealify_realify]
  simp_rw [e2, e3] at this
  exact this

end

-- ===== from Q3g.lean =====
section

theorem isHermitian_sesq {r M : ℕ} {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) (c : ℝ)
    (H : Matrix (Fin r) (Fin M) ℂ) :
    ((c : ℂ) • (H * A * Hᴴ) - ((c : ℂ) * A.trace) • (1 : Matrix (Fin r) (Fin r) ℂ)).IsHermitian := by
  have htr : star A.trace = A.trace := by rw [← trace_conjTranspose, hA.eq]
  unfold IsHermitian
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, conjTranspose_mul,
    conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, conjTranspose_one, star_mul', htr,
    Complex.star_def, Complex.conj_ofReal, Matrix.mul_assoc]

theorem isHermitian_gue {r : ℕ} (Z : Fin r → Fin r → ℂ) :
    ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

theorem continuous_sesq {r M : ℕ} (A : Matrix (Fin M) (Fin M) ℂ) (a b : ℂ) :
    Continuous (fun X : Fin M → Fin r → ℂ =>
      a • ((Matrix.of X)ᵀ * A * ((Matrix.of X)ᵀ)ᴴ) - b • (1 : Matrix (Fin r) (Fin r) ℂ)) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  simp only [Matrix.sub_apply, Matrix.smul_apply, mul_apply, conjTranspose_apply,
    transpose_apply, Matrix.of_apply, smul_eq_mul]
  fun_prop

theorem continuous_gue {r : ℕ} :
    Continuous (fun Z : Fin r → Fin r → ℂ => (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  simp only [Matrix.add_apply, Matrix.smul_apply, conjTranspose_apply, Matrix.of_apply, smul_eq_mul]
  fun_prop

/-- **Q3** (CLT for Gaussian sesquilinear forms), proved. -/
theorem q3_sesqCLT : Q3_sesqCLT := by
  unfold Q3_sesqCLT
  intro r C s₀ hs₀ M hM A hAh hC hs f hf hfB
  have hMpos : ∀ n, (0 : ℝ) < M n := by
    intro n
    rcases Nat.eq_zero_or_pos (M n) with h | h
    · have h0 : ((M n : ℕ) : ℝ) = 0 := by exact_mod_cast h
      have := hs n
      rw [h0, div_zero] at this
      linarith
    · exact_mod_cast h
  set s : ℕ → ℝ := fun n => Real.sqrt (((A n * A n).trace).re / M n) with hsdef
  have hspos : ∀ n, 0 < s n := fun n => Real.sqrt_pos.mpr (lt_of_lt_of_le hs₀ (hs n))
  have hs2 : ∀ n, s n ^ 2 = ((A n * A n).trace).re / M n :=
    fun n => Real.sq_sqrt (le_trans hs₀.le (hs n))
  set c : ℕ → ℝ := fun n => Real.sqrt (M n) / s n / M n with hcdef
  have hT : ∀ n (X : Fin (M n) → Fin r → ℂ),
      ((Real.sqrt (M n) / s n : ℝ) : ℂ) • ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
        ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ)) =
      ((c n : ℝ) : ℂ) • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
        (((c n : ℝ) : ℂ) * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    intro n X
    rw [smul_sub, smul_smul, smul_smul]
    congr 2
    · simp only [hcdef]; push_cast; ring
    · simp only [hcdef]; push_cast; ring
  have hce : ∀ n, c n = (s n)⁻¹ * (Real.sqrt (M n))⁻¹ := by
    intro n
    have hsq : Real.sqrt (M n) * Real.sqrt (M n) = M n := Real.mul_self_sqrt (hMpos n).le
    have hsqp : 0 < Real.sqrt (M n) := Real.sqrt_pos.mpr (hMpos n)
    calc c n = Real.sqrt (M n) / s n / (Real.sqrt (M n) * Real.sqrt (M n)) := by rw [hsq]
      _ = (s n)⁻¹ * (Real.sqrt (M n))⁻¹ := by field_simp [hsqp.ne', (hspos n).ne']
  refine levy_matrix (Ω := fun n => Fin (M n) → Fin r → ℂ)
    (fun n => SpikedWishart.SoftEdge.sampleLaw (M n) r) (SpikedWishart.SoftEdge.sampleLaw r r)
    (fun n X => ((Real.sqrt (M n) / s n : ℝ) : ℂ) •
      ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
        ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ))) ?_ ?_
    (fun Z => (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)) ?_ ?_ ?_ f hf hfB
  · intro n
    apply ((continuous_realify r).comp _).measurable
    exact (continuous_sesq (A n) _ _).congr (fun X => (hT n X).symm)
  · intro n X
    beta_reduce
    rw [hT]
    exact isHermitian_sesq (hAh n) (c n) _
  · exact ((continuous_realify r).comp continuous_gue).measurable
  · intro Z; exact isHermitian_gue Z
  · intro B hB
    have e1 : ∀ n, ∫ X, cexp (((trace (B * (((Real.sqrt (M n) / s n : ℝ) : ℂ) •
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
            ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ))))).re : ℂ) * I)
          ∂SpikedWishart.SoftEdge.sampleLaw (M n) r =
        ∏ m, ∏ j, (cexp (-(((c n * hB.eigenvalues j * (hAh n).eigenvalues m : ℝ) : ℂ) * I)) /
          (1 - ((c n * hB.eigenvalues j * (hAh n).eigenvalues m : ℝ) : ℂ) * I)) := by
      intro n
      simp_rw [hT n]
      exact charT (hAh n) hB (c n)
    simp only [e1, gue_char r hB]
    have hc0 : ∀ n, 0 ≤ c n := fun n => by
      simp only [hcdef]; exact div_nonneg (div_nonneg (Real.sqrt_nonneg _) (hspos n).le) (hMpos n).le
    apply prod_phi_tendsto M (fun n m j => c n * hB.eigenvalues j * (hAh n).eigenvalues m) (pair B B)
      (fun n => c n * (∑ j, |hB.eigenvalues j|) * C)
    · -- c n → 0
      have hcb : ∀ n, c n ≤ (Real.sqrt s₀)⁻¹ * (Real.sqrt (M n))⁻¹ := by
        intro n
        have hsqp : 0 < Real.sqrt (M n) := Real.sqrt_pos.mpr (hMpos n)
        rw [hce n]
        have hss : Real.sqrt s₀ ≤ s n := Real.sqrt_le_sqrt (hs n)
        have hs0p : 0 < Real.sqrt s₀ := Real.sqrt_pos.mpr hs₀
        exact mul_le_mul_of_nonneg_right (inv_anti₀ hs0p hss) (inv_nonneg.mpr hsqp.le)
      have hlim : Tendsto (fun n => (Real.sqrt s₀)⁻¹ * (Real.sqrt (M n))⁻¹) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop.comp hM))).const_mul (Real.sqrt s₀)⁻¹
        simpa using this
      have hct : Tendsto c atTop (𝓝 0) := squeeze_zero hc0 hcb hlim
      have := (hct.mul_const (∑ j, |hB.eigenvalues j|)).mul_const C
      simpa using this
    · intro n m j
      have hd := abs_eig_le (hAh n) C (hC n) m
      have hl : |hB.eigenvalues j| ≤ ∑ j, |hB.eigenvalues j| :=
        Finset.single_le_sum (f := fun j => |hB.eigenvalues j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ j)
      rw [abs_mul, abs_mul, abs_of_nonneg (hc0 n)]
      have hΛ : 0 ≤ ∑ j, |hB.eigenvalues j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hl (hc0 n)) hd (abs_nonneg _)
        (mul_nonneg (hc0 n) hΛ)
    · intro n
      have hd : ∑ m, (hAh n).eigenvalues m ^ 2 = s n ^ 2 * M n := by
        rw [← pair_herm_eq_sum_sq, pair_eq_trace, (hAh n).eq, hs2]
        field_simp [(hMpos n).ne']
      have hl : ∑ j, hB.eigenvalues j ^ 2 = pair B B := (pair_herm_eq_sum_sq hB).symm
      have e2 : ∑ m, ∑ j, (c n * hB.eigenvalues j * (hAh n).eigenvalues m) ^ 2 =
          c n ^ 2 * (∑ m, (hAh n).eigenvalues m ^ 2) * (∑ j, hB.eigenvalues j ^ 2) := by
        calc ∑ m, ∑ j, (c n * hB.eigenvalues j * (hAh n).eigenvalues m) ^ 2
            = ∑ m, (c n ^ 2 * (hAh n).eigenvalues m ^ 2) * ∑ j, hB.eigenvalues j ^ 2 := by
              refine Finset.sum_congr rfl (fun m _ => ?_)
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              ring
          _ = (∑ m, c n ^ 2 * (hAh n).eigenvalues m ^ 2) * ∑ j, hB.eigenvalues j ^ 2 :=
              (Finset.sum_mul _ _ _).symm
          _ = c n ^ 2 * (∑ m, (hAh n).eigenvalues m ^ 2) * (∑ j, hB.eigenvalues j ^ 2) := by
              rw [← Finset.mul_sum]
      have e3 : c n ^ 2 * (s n ^ 2 * M n) = 1 := by
        rw [hce n, mul_pow, inv_pow, inv_pow, Real.sq_sqrt (hMpos n).le]
        field_simp [(hMpos n).ne', (hspos n).ne']
      rw [e2, hd, hl, e3, one_mul]

end

end SpikedWishart.Separated.Lib

open SpikedWishart.Separated in
theorem solution :
  ∀ (r : ℕ) (C s₀ : ℝ), 0 < s₀ → ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    ∀ f : Matrix (Fin r) (Fin r) ℂ → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
    Tendsto (fun n => ∫ X, f (((Real.sqrt (M n) / Real.sqrt (((A n * A n).trace).re / M n) : ℝ) : ℂ) •
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
            ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ)))
        ∂(SpikedWishart.SoftEdge.sampleLaw (M n) r))
      atTop (𝓝 (∫ Z, f ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ))
        ∂(SpikedWishart.SoftEdge.sampleLaw r r))) := by
  exact SpikedWishart.Separated.Lib.q3_sesqCLT
