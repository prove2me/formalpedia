-- Prove2me | solution 1 for RandomGradFree.Smooth.oracle_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:31:10.936307+00:00
-- url     : https://prove2.me/submissions/4dae8db6-4510-4366-b4aa-4f18ce42b85f

import Definitions.Def_RandomGradFree_Shared_oracle
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Smooth_symOracle
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic
import Mathlib.Probability.Moments.MGFAnalytic

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

namespace RandomProof
open MeasureTheory ProbabilityTheory RandomGradFree.Accelerated

theorem d5 : deriv (fun t : ℝ => (3+6*t^2+t^4)*Real.exp (t^2/2)) =
    fun t => (15*t+10*t^3+t^5)*Real.exp (t^2/2) := by
  have hh := aux_dos_hasDeriv (fun t => 3+6*t^2+t^4) (fun t => 12*t+4*t^3)
    (fun t => (((hasDerivAt_pow 2 t).const_mul 6).const_add 3 |>.add (hasDerivAt_pow 4 t)).congr_deriv (by norm_num; ring))
  rw [hh]
  funext t
  ring

theorem d6 : deriv (fun t : ℝ => (15*t+10*t^3+t^5)*Real.exp (t^2/2)) =
    fun t => (15+45*t^2+15*t^4+t^6)*Real.exp (t^2/2) := by
  have hh := aux_dos_hasDeriv (fun t => 15*t+10*t^3+t^5) (fun t => 15+30*t^2+5*t^4)
    (fun t => (((hasDerivAt_id t).const_mul 15).add ((hasDerivAt_pow 3 t).const_mul 10) |>.add
      (hasDerivAt_pow 5 t)).congr_deriv (by norm_num; ring))
  rw [hh]
  funext t
  ring

theorem moment6 : ∫ t, t^6 ∂(gaussianReal 0 1) = 15 := by
  have hh := iteratedDeriv_mgf_zero (X := fun t : ℝ => t) (μ := gaussianReal 0 1) (by simp) 6
  rw [aux_dos_mgf,iteratedDeriv_succ',aux_dos_d1,iteratedDeriv_succ',aux_dos_d2,
    iteratedDeriv_succ',aux_dos_d3,iteratedDeriv_succ',aux_dos_d4,
    iteratedDeriv_succ',d5,iteratedDeriv_one,d6] at hh
  simpa using hh.symm

theorem triple_moment {ι : Type*} [Fintype ι] [DecidableEq ι] (i j k : ι) :
    (∏ l : ι, ∫ t : ℝ, t^((if l=i then 2 else 0)+(if l=j then 2 else 0)+(if l=k then 2 else 0)) ∂(gaussianReal 0 1)) =
      1+2*(if i=j then 1 else 0)+2*(if i=k then 1 else 0)+2*(if j=k then 1 else 0)+
        8*(if i=j ∧ i=k then 1 else 0) := by
  by_cases hij : i=j
  · subst j
    by_cases hik : i=k
    · subst k
      rw [Finset.prod_eq_single i]
      · norm_num [moment6]
      · intro l hl hli; simp [hli]
      · simp
    · rw [Finset.prod_eq_single i]
      · norm_num [hik,aux_dos_m4]
      · intro l hl hli
        by_cases hlk : l=k <;> simp [hli,hlk,hik,Ne.symm hik,aux_dos_m2]
      · simp
  · by_cases hik : i=k
    · subst k
      rw [Finset.prod_eq_single i]
      · norm_num [hij,Ne.symm hij,aux_dos_m4]
      · intro l hl hli
        by_cases hlj : l=j <;> simp [hli,hlj,hij,Ne.symm hij,aux_dos_m2]
      · simp
    · by_cases hjk : j=k
      · subst k
        rw [Finset.prod_eq_single j]
        · norm_num [hij,Ne.symm hij,aux_dos_m4]
        · intro l hl hlj
          by_cases hli : l=i <;> simp [hli,hlj,hij,Ne.symm hij,aux_dos_m2]
        · simp
      · rw [Finset.prod_eq_one]
        · simp [hij,hik,hjk]
        · intro l hl
          by_cases hli : l=i <;> by_cases hlj : l=j <;> by_cases hlk : l=k <;>
            simp_all [aux_dos_m2]

theorem norm6_exact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖^6 ∂(stdGaussian E) =
      (Module.finrank ℝ E : ℝ)^3+6*(Module.finrank ℝ E : ℝ)^2+8*(Module.finrank ℝ E : ℝ) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let powr (i j k l : Fin (Module.finrank ℝ E)) : ℕ := (if l=i then 2 else 0)+(if l=j then 2 else 0)+(if l=k then 2 else 0)
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,integral_map (Measurable.aemeasurable (by fun_prop))
    (by fun_prop : Continuous (fun u : E => ‖u‖^6)).aestronglyMeasurable]
  have hnorm (z : Fin (Module.finrank ℝ E) → ℝ) : ‖∑ i, z i • b i‖^6 =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E), ∏ l : Fin (Module.finrank ℝ E), z l^(powr i j k l) := by
    have hs : ‖∑ i, z i • b i‖^2 = ∑ i, z i^2 := by
      rw [← real_inner_self_eq_norm_sq,b.orthonormal.inner_sum]
      simp [pow_two]
    rw [show ‖∑ i, z i • b i‖^6 = (‖∑ i, z i • b i‖^2)^3 by ring,hs]
    simp only [powr,pow_add,Finset.prod_mul_distrib,pow_ite,pow_zero,Finset.prod_ite_eq',Finset.mem_univ,if_true]
    simp only [pow_succ,pow_zero,mul_one,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    ring
  simp_rw [hnorm]
  have hint (i j k : Fin (Module.finrank ℝ E)) : Integrable (fun z : Fin (Module.finrank ℝ E) → ℝ => ∏ l, z l^(powr i j k l))
      (Measure.pi fun _ => gaussianReal 0 1) := Integrable.fintype_prod (fun l => aux_dos_int_pow _)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint i j k)))]
  have hin (i j k : Fin (Module.finrank ℝ E)) :
      (∫ z : Fin (Module.finrank ℝ E) → ℝ, ∏ l, z l^(powr i j k l) ∂(Measure.pi fun _ => gaussianReal 0 1)) =
      ∏ l, ∫ t : ℝ, t^(powr i j k l) ∂(gaussianReal 0 1) :=
    integral_fintype_prod_eq_prod (fun l (t : ℝ) => t^(powr i j k l))
  have hi2 (i : Fin (Module.finrank ℝ E)) := integral_finsetSum Finset.univ
    (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hint i j k))
  simp_rw [hi2]
  have hi3 (i j : Fin (Module.finrank ℝ E)) := integral_finsetSum Finset.univ (fun k _ => hint i j k)
  simp_rw [hi3,hin]
  simp_rw [powr,triple_moment]
  simp [Finset.sum_add_distrib,Finset.mul_sum,ite_and]
  ring

end RandomProof

theorem RandomProof.directional_bound {E : Type*} [NormedAddCommGroup E]
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


open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

open scoped RealInnerProductSpace

theorem aux_sa_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖) (x v : E) :
    |f (x + v) - f x - ⟪gradient f x, v⟫| ≤ L₁ / 2 * ‖v‖ ^ 2 := by
  let g : ℝ → ℝ := fun t => f (x + t • v) - f x - t * ⟪gradient f x, v⟫
  let g' : ℝ → ℝ := fun t => ⟪gradient f (x + t • v), v⟫ - ⟪gradient f x, v⟫
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f (x + t • v)))
        (x + t • v) :=
      hasGradientAt_iff_hasFDerivAt.mp (hdiff (x + t • v)).hasGradientAt
    have h3 := h2.comp_hasDerivAt t h1
    have h4 : HasDerivAt g
        ((InnerProductSpace.toDual ℝ E (gradient f (x + t • v))) v - 1 * ⟪gradient f x, v⟫) t :=
      (h3.sub_const (f x)).sub ((hasDerivAt_id' t).mul_const _)
    refine h4.congr_deriv ?_
    simp [g']
  let B : ℝ → ℝ := fun t => L₁ / 2 * ‖v‖ ^ 2 * t ^ 2
  let B' : ℝ → ℝ := fun t => L₁ * ‖v‖ ^ 2 * t
  have hB : ∀ t, HasDerivAt B (B' t) t := by
    intro t
    have h : HasDerivAt B (L₁ / 2 * ‖v‖ ^ 2 * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) t :=
      (hasDerivAt_pow 2 t).const_mul _
    refine h.congr_deriv ?_
    simp only [B']; norm_num; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := g)
    (f' := g')
    (fun t _ => (hg t).continuousAt.continuousWithinAt)
    (fun t _ => (hg t).hasDerivWithinAt) (B := B) (B' := B') (by simp [g, B]) hB ?_
    (x := 1) (by simp)
  · simpa [g, B, Real.norm_eq_abs] using key
  · intro t ht
    rw [Real.norm_eq_abs]
    have : g' t = ⟪gradient f (x + t • v) - gradient f x, v⟫ := by simp [g', inner_sub_left]
    rw [this]
    calc |⟪gradient f (x + t • v) - gradient f x, v⟫|
        ≤ ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (L₁ * ‖x + t • v - x‖) * ‖v‖ := by gcongr; exact hgrad _ _
      _ = B' t := by simp [B', norm_smul, abs_of_nonneg ht.1]; ring

theorem aux_sa_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ E
  have hmem : MemLp (id : E → E) 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hone : ∀ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h := covarianceBilin_apply hmem (b i) (b i)
    rw [covarianceBilin_stdGaussian] at h
    have hm : (stdGaussian E)[id] = 0 := by simp
    simp only [hm, sub_zero] at h
    change ⟪b i, b i⟫ = _ at h
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i] at h
    simp only [one_pow] at h
    rw [h]
    congr 1
    ext u
    ring
  have hint : ∀ i, Integrable (fun u => ⟪b i, u⟫ ^ 2) (stdGaussian E) := by
    intro i
    have : MemLp (fun u : E => ⟪b i, u⟫) 2 (stdGaussian E) :=
      (innerSL ℝ (b i)).comp_memLp' hmem
    exact this.integrable_sq
  calc ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E)
      = ∫ u, ∑ i, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := by
        congr 1; ext u; rw [b.sum_sq_inner_right]
    _ = ∑ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := integral_finsetSum _ (fun i _ => hint i)
    _ = Module.finrank ℝ E := by simp [hone]

end RandomGradFree.Smooth

open RandomGradFree.Smooth
open MeasureTheory ProbabilityTheory
namespace RandomProof
open MeasureTheory ProbabilityTheory RandomGradFree.Shared RandomGradFree.Smooth
open scoped RealInnerProductSpace

theorem convex_tangent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x v : E) :
    0 ≤ f (x+v)-f x-inner ℝ (gradient f x) v := by
  let g : ℝ → ℝ := fun t => f (x+t • v)
  have hg : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ,?_⟩
    intro a ha b hb p q hp hq hpq
    have hh := hf.2 (Set.mem_univ (x+a • v)) (Set.mem_univ (x+b • v)) hp hq hpq
    have he : x+(p*a+q*b) • v = p • (x+a • v)+q • (x+b • v) := by
      calc
        _ = (p+q) • x+(p*a+q*b) • v := by rw [hpq,one_smul]
        _ = _ := by module
    simpa only [g,smul_eq_mul,he] using hh
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hdg : HasDerivAt g (inner ℝ (gradient f x) v) 0 := by
    have hh := (hd (x+0 • v)).hasFDerivAt.comp_hasDerivAt 0 hline
    convert! hh using 1 <;> simp [g,inner_gradient_left]
  have hh := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hdg
  simp [g,slope_def_field] at hh
  rw [inner_gradient_left]
  linarith

theorem square_error (r s D : ℝ) (hD : 0 ≤ D) (h : |r-s| ≤ D) :
    r^2 ≤ 2*s^2+2*D^2 := by
  have hh := mul_self_le_mul_self (abs_nonneg (r-s)) h
  rw [← sq, sq_abs, ← sq] at hh
  nlinarith [sq_nonneg (r-2*s)]

theorem oracle_point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 < μ) (x u : E) :
    ‖oracle f μ x u‖^2 ≤ μ^2/2*L^2*‖u‖^6+2*‖fderiv ℝ f x u • u‖^2 := by
  have hb := aux_sa_descent f L hd hgrad x (μ • u)
  rw [inner_smul_right,norm_smul,Real.norm_of_nonneg hμ.le] at hb
  have he : (f (x+μ • u)-f x)/μ-inner ℝ (gradient f x) u =
      (f (x+μ • u)-f x-μ*inner ℝ (gradient f x) u)/μ := by field_simp
  have hb' : |(f (x+μ • u)-f x)/μ-inner ℝ (gradient f x) u| ≤ L*μ/2*‖u‖^2 := by
    rw [he,abs_div,abs_of_pos hμ,div_le_iff₀ hμ]
    nlinarith [hb]
  have hh := square_error _ _ _ (by positivity : 0 ≤ L*μ/2*‖u‖^2) hb'
  have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖u‖)
  simp only [oracle,if_neg hμ.ne',norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← inner_gradient_left]
  nlinarith [hh']

theorem symmetric_point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f) (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 < μ) (x u : E) :
    ‖symOracle f μ x u‖^2 ≤ μ^2/8*L^2*‖u‖^6+2*‖fderiv ℝ f x u • u‖^2 := by
  let a := f (x+μ • u)-f x-μ*inner ℝ (gradient f x) u
  let b := f (x-μ • u)-f x+μ*inner ℝ (gradient f x) u
  have ha0 : 0 ≤ a := by
    simpa [a,inner_smul_right] using convex_tangent f hf hd x (μ • u)
  have hb0 : 0 ≤ b := by
    simpa [b,sub_eq_add_neg,inner_neg_right,inner_smul_right] using convex_tangent f hf hd x (-(μ • u))
  have ha : a ≤ L/2*(μ*‖u‖)^2 := by
    have hh := aux_sa_descent f L hd hgrad x (μ • u)
    rw [inner_smul_right,norm_smul,Real.norm_of_nonneg hμ.le] at hh
    exact (le_abs_self a).trans hh
  have hb : b ≤ L/2*(μ*‖u‖)^2 := by
    have hh := aux_sa_descent f L hd hgrad x (-(μ • u))
    have hbabs : |b| ≤ L/2*(μ*‖u‖)^2 := by
      simpa [b,sub_eq_add_neg,inner_neg_right,inner_smul_right,norm_smul,Real.norm_of_nonneg hμ.le] using hh
    exact (le_abs_self b).trans hbabs
  have hab : |a-b| ≤ L/2*(μ*‖u‖)^2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : (f (x+μ • u)-f (x-μ • u))/(2*μ)-inner ℝ (gradient f x) u = (a-b)/(2*μ) := by
    dsimp [a,b]
    field_simp
    ring
  have hb' : |(f (x+μ • u)-f (x-μ • u))/(2*μ)-inner ℝ (gradient f x) u| ≤ L*μ/4*‖u‖^2 := by
    rw [he,abs_div,abs_of_pos (by positivity : 0<2*μ),div_le_iff₀ (by positivity : 0<2*μ)]
    nlinarith [hab]
  have hh := square_error _ _ _ (by positivity : 0 ≤ L*μ/4*‖u‖^2) hb'
  have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖u‖)
  simp only [symOracle,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← inner_gradient_left]
  nlinarith [hh']

end RandomProof

namespace RandomProof
open MeasureTheory ProbabilityTheory RandomGradFree.Shared RandomGradFree.Smooth

theorem directional_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (L : E →L[ℝ] ℝ) :
    Integrable (fun u : E => ‖L u • u‖^2) (stdGaussian E) := by
  have h4 : Integrable (fun u : E => ‖u‖^4) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (4:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  refine Integrable.mono' (h4.const_mul (‖L‖^2)) (by fun_prop) (Filter.Eventually.of_forall (fun u => ?_))
  have hh : ‖L u • u‖ ≤ ‖L‖*‖u‖^2 := by
    rw [norm_smul]
    have hh := mul_le_mul_of_nonneg_right (L.le_opNorm u) (norm_nonneg u)
    nlinarith [hh]
  have hh' := mul_self_le_mul_self (norm_nonneg _) hh
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [hh']

theorem integrate_point_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : E → E) (f : E → ℝ) (x : E) (hd : DifferentiableAt ℝ f x) (A : ℝ)
    (hF : ∀ u, ‖F u‖^2 ≤ A*‖u‖^6+2*‖fderiv ℝ f x u • u‖^2) :
    ∫ u, ‖F u‖^2 ∂(stdGaussian E) ≤
      A*((Module.finrank ℝ E:ℝ)^3+6*(Module.finrank ℝ E:ℝ)^2+8*(Module.finrank ℝ E:ℝ))+
      2*((Module.finrank ℝ E:ℝ)+4)*‖gradient f x‖^2 := by
  have h6 : Integrable (fun u : E => ‖u‖^6) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (6:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  have hdir := directional_integrable (fderiv ℝ f x)
  calc
    _ ≤ ∫ u, (A*‖u‖^6+2*‖fderiv ℝ f x u • u‖^2) ∂(stdGaussian E) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg _))
        ((h6.const_mul A).add (hdir.const_mul 2)) (Filter.Eventually.of_forall hF)
    _ = A*((Module.finrank ℝ E:ℝ)^3+6*(Module.finrank ℝ E:ℝ)^2+8*(Module.finrank ℝ E:ℝ))+
        2*(∫ u, ‖fderiv ℝ f x u • u‖^2 ∂(stdGaussian E)) := by
      rw [integral_add (h6.const_mul A) (hdir.const_mul 2),integral_const_mul,integral_const_mul,norm6_exact]
    _ ≤ _ := by
      have hh := directional_bound f x hd
      linarith

theorem oracle_moments {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f) (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    (∫ u, ‖oracle f μ x u‖^2 ∂(stdGaussian E) ≤ μ^2/2*L^2*((Module.finrank ℝ E:ℝ)+6)^3+
      2*((Module.finrank ℝ E:ℝ)+4)*‖gradient f x‖^2) ∧
    (∫ u, ‖symOracle f μ x u‖^2 ∂(stdGaussian E) ≤ μ^2/8*L^2*((Module.finrank ℝ E:ℝ)+6)^3+
      2*((Module.finrank ℝ E:ℝ)+4)*‖gradient f x‖^2) := by
  have hn : 0 ≤ (Module.finrank ℝ E:ℝ) := Nat.cast_nonneg _
  have hpoly : (Module.finrank ℝ E:ℝ)^3+6*(Module.finrank ℝ E:ℝ)^2+8*(Module.finrank ℝ E:ℝ) ≤
      ((Module.finrank ℝ E:ℝ)+6)^3 := by nlinarith [sq_nonneg (Module.finrank ℝ E:ℝ)]
  constructor
  · exact (integrate_point_bound (fun u => oracle f μ x u) f x (hd x) (μ^2/2*L^2)
      (oracle_point f L hL hd hgrad μ hμ x)).trans
        (add_le_add (mul_le_mul_of_nonneg_left hpoly (by positivity)) le_rfl)
  · exact (integrate_point_bound (fun u => symOracle f μ x u) f x (hd x) (μ^2/8*L^2)
      (symmetric_point f hf L hL hd hgrad μ hμ x)).trans
        (add_le_add (mul_le_mul_of_nonneg_left hpoly (by positivity)) le_rfl)

end RandomProof

namespace RandomGradFree.Smooth

theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    ∫ u, ‖RandomGradFree.Shared.oracle f μ x u‖ ^ 2 ∂(stdGaussian E)
        ≤ μ ^ 2 / 2 * L₁ ^ 2 * ((Module.finrank ℝ E : ℝ) + 6) ^ 3
          + 2 * ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient f x‖ ^ 2 ∧
      ∫ u, ‖symOracle f μ x u‖ ^ 2 ∂(stdGaussian E)
        ≤ μ ^ 2 / 8 * L₁ ^ 2 * ((Module.finrank ℝ E : ℝ) + 6) ^ 3
          + 2 * ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient f x‖ ^ 2 := by
  exact RandomProof.oracle_moments f hf L₁ hL₁ hdiff hgrad μ hμ x

end RandomGradFree.Smooth
