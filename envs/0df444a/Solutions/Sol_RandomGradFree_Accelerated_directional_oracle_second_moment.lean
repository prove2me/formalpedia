-- Prove2me | solution 1 for RandomGradFree.Accelerated.directional_oracle_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:56:00.970709+00:00
-- url     : https://prove2.me/submissions/0e53a3a7-245f-4ae2-8a63-ec121e5c4c35

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

lemma aux_dos_hasDeriv (p p' : ℝ → ℝ) (h : ∀ t, HasDerivAt p (p' t) t) :
    deriv (fun t => p t * Real.exp (t ^ 2 / 2))
      = fun t => (p' t + p t * t) * Real.exp (t ^ 2 / 2) := by
  funext t
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t :=
    ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by norm_num)
  have h3 : HasDerivAt (fun t => p t * Real.exp (t ^ 2 / 2)) _ t := (h t).mul h2.exp
  rw [h3.deriv]
  ring

lemma aux_dos_mgf :
    mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t => 1 * Real.exp (t ^ 2 / 2) := by
  rw [mgf_fun_id_gaussianReal]
  funext t
  simp

lemma aux_dos_d1 : deriv (fun t : ℝ => 1 * Real.exp (t ^ 2 / 2))
    = fun t => t * Real.exp (t ^ 2 / 2) := by
  have := aux_dos_hasDeriv (fun _ => 1) (fun _ => 0) (fun t => hasDerivAt_const t 1)
  rw [this]
  funext t
  ring

lemma aux_dos_d2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2))
    = fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
  have := aux_dos_hasDeriv (fun t => t) (fun _ => 1) (fun t => hasDerivAt_id t)
  rw [this]
  funext t
  ring

lemma aux_dos_d3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2))
    = fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
  have := aux_dos_hasDeriv (fun t => 1 + t ^ 2) (fun t => 2 * t)
    (fun t => ((hasDerivAt_pow 2 t).const_add 1).congr_deriv (by norm_num))
  rw [this]
  funext t
  ring

lemma aux_dos_d4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2))
    = fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
  have := aux_dos_hasDeriv (fun t => 3 * t + t ^ 3) (fun t => 3 + 3 * t ^ 2)
    (fun t => (((hasDerivAt_id t).const_mul 3).add (hasDerivAt_pow 3 t)).congr_deriv
      (by norm_num))
  rw [this]
  funext t
  ring

lemma aux_dos_m2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 2
  rw [aux_dos_mgf, iteratedDeriv_succ', aux_dos_d1, iteratedDeriv_one, aux_dos_d2] at h
  simp at h
  rw [← h]

lemma aux_dos_m4 : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 4
  rw [aux_dos_mgf, iteratedDeriv_succ', aux_dos_d1, iteratedDeriv_succ', aux_dos_d2,
    iteratedDeriv_succ', aux_dos_d3, iteratedDeriv_one, aux_dos_d4] at h
  simp at h
  rw [← h]

lemma aux_dos_int_pow (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) k

lemma aux_dos_main {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E) (i0 : ι) :
    ∫ u, inner ℝ (b i0) u ^ 2 * ‖u‖ ^ 2 ∂(stdGaussian E) = (Fintype.card ι : ℝ) + 2 := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, integral_map (Measurable.aemeasurable (by fun_prop))
    (by fun_prop : Continuous fun u : E => inner ℝ (b i0) u ^ 2 * ‖u‖ ^ 2).aestronglyMeasurable]
  let e : ι → ι → ℕ := fun j i => (if i = i0 then 2 else 0) + (if i = j then 2 else 0)
  have key : ∀ x : ι → ℝ, inner ℝ (b i0) (∑ i, x i • b i) ^ 2 * ‖∑ i, x i • b i‖ ^ 2
      = ∑ j, ∏ i, x i ^ (e j i) := by
    intro x
    rw [b.orthonormal.inner_right_fintype, ← real_inner_self_eq_norm_sq,
      b.orthonormal.inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [e, pow_add, Finset.prod_mul_distrib, pow_ite, pow_zero, Finset.prod_ite_eq',
      Finset.mem_univ, if_true, conj_trivial]
    ring
  simp_rw [key]
  rw [integral_finsetSum _ (fun j _ => Integrable.fintype_prod (fun i => aux_dos_int_pow _))]
  have hprod : ∀ j, ∫ x : ι → ℝ, ∏ i, x i ^ (e j i) ∂(Measure.pi fun _ => gaussianReal 0 1)
      = ∏ i, ∫ t, t ^ (e j i) ∂(gaussianReal 0 1) :=
    fun j => integral_fintype_prod_eq_prod (fun i (t : ℝ) => t ^ (e j i))
  simp_rw [hprod]
  have hval : ∀ j, ∏ i, ∫ t, t ^ (e j i) ∂(gaussianReal 0 1)
      = 1 + (if j = i0 then 2 else 0) := by
    intro j
    by_cases hj : j = i0
    · subst hj
      rw [Finset.prod_eq_single j]
      · simp [e, aux_dos_m4]; norm_num
      · intro i _ hi
        simp [e, hi]
      · simp
    · rw [Finset.prod_eq_one]
      · simp [hj]
      · intro i _
        by_cases h1 : i = i0 <;> by_cases h2 : i = j <;> simp_all [e, aux_dos_m2]
  simp_rw [hval]
  rw [Finset.sum_add_distrib]
  simp

end RandomGradFree.Accelerated

open RandomGradFree.Accelerated

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) (hfx : DifferentiableAt ℝ f x) :
    ∫ u, ‖fderiv ℝ f x u • u‖ ^ 2 ∂(stdGaussian E)
      ≤ ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient f x‖ ^ 2 := by
  classical
  set g := gradient f x with hg_def
  have hL : ∀ u, fderiv ℝ f x u = inner ℝ g u := fun u => (inner_gradient_left).symm
  have hint : ∀ u, ‖fderiv ℝ f x u • u‖ ^ 2 = inner ℝ g u ^ 2 * ‖u‖ ^ 2 := by
    intro u
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hL]
  simp_rw [hint]
  by_cases hg0 : g = 0
  · simp [hg0]
  set e : E := ‖g‖⁻¹ • g with he_def
  have hgn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg0
  have hge : g = ‖g‖ • e := by
    rw [he_def, smul_smul, mul_inv_cancel₀ hgn, one_smul]
  have hen : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hgn]
  have hon : Orthonormal ℝ ((↑) : ({e} : Set E) → E) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rw [Set.mem_singleton_iff] at hi hj
    subst hi hj
    simp [hen]
  obtain ⟨u, b, hsub, hb⟩ := hon.exists_orthonormalBasis_extension
  let i0 : u := ⟨e, hsub (Set.mem_singleton e)⟩
  have hbi0 : b i0 = e := by rw [hb]
  have hcard : (Fintype.card u : ℝ) = Module.finrank ℝ E := by
    rw [Module.finrank_eq_card_basis b.toBasis]
  have h1 : ∀ v : E, inner ℝ g v ^ 2 * ‖v‖ ^ 2 = ‖g‖ ^ 2 * (inner ℝ (b i0) v ^ 2 * ‖v‖ ^ 2) := by
    intro v
    rw [hbi0]
    conv_lhs => rw [hge, real_inner_smul_left]
    ring
  simp_rw [h1]
  rw [integral_const_mul, aux_dos_main b i0, hcard]
  nlinarith [sq_nonneg ‖g‖]
