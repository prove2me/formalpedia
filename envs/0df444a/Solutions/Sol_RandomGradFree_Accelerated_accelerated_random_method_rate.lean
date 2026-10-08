-- Prove2me | solution 1 for RandomGradFree.Accelerated.accelerated_random_method_rate
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T18:08:01.651096+00:00
-- url     : https://prove2.me/submissions/030c4280-51ff-4622-b509-03f100d4410f

import Mathlib
import Definitions.Def_RandomGradFree_Accelerated_psi
import Definitions.Def_RandomGradFree_Accelerated_C
import Definitions.Def_RandomGradFree_Accelerated_IsAcceleratedRandomRun
import Definitions.Def_RandomGradFree_Shared_oracle
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Smooth_symOracle
import Definitions.Def_RandomGradFree_Smooth_IsRandomGradientRun

set_option autoImplicit false

/- Complete checked assembly: AttributedAnalytic -/
section

section

open _root_.RandomGradFree.Smooth
namespace AcceleratedSource.OracleMoment

-- Prove2me | solution 1 for RandomGradFree.Accelerated.oracle_second_moment_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:35:55.0523+00:00
-- url     : https://prove2.me/submissions/b6d8e359-e5c5-4a2c-999f-73899083ea96


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

open _root_.AcceleratedSource.OracleMoment.RandomGradFree.Accelerated

namespace RandomProof
open MeasureTheory ProbabilityTheory _root_.AcceleratedSource.OracleMoment.RandomGradFree.Accelerated

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
        by_cases hlk : l=k <;> simp [hli,hlk,Ne.symm hik,aux_dos_m2]
      · simp
  · by_cases hik : i=k
    · subst k
      rw [Finset.prod_eq_single i]
      · norm_num [hij,Ne.symm hij,aux_dos_m4]
      · intro l hl hli
        by_cases hlj : l=j <;> simp [hli,hlj,Ne.symm hij,aux_dos_m2]
      · simp
    · by_cases hjk : j=k
      · subst k
        rw [Finset.prod_eq_single j]
        · norm_num [hij,Ne.symm hij,aux_dos_m4]
        · intro l hl hlj
          by_cases hli : l=i <;> simp [hli,hlj,hij,aux_dos_m2]
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
    simp only [pow_succ,pow_zero,Finset.sum_mul,Finset.mul_sum]
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
  simp [Finset.sum_add_distrib,ite_and]
  ring

end RandomProof

theorem RandomProof.directional_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) (_hfx : DifferentiableAt ℝ f x) :
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

open _root_.AcceleratedSource.OracleMoment.RandomGradFree.Smooth
open MeasureTheory ProbabilityTheory
namespace RandomProof
open MeasureTheory ProbabilityTheory _root_.RandomGradFree.Shared _root_.AcceleratedSource.OracleMoment.RandomGradFree.Smooth
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
    convert! hh using 1
    simp [inner_gradient_left]
  have hh := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hdg
  simp [g,slope_def_field] at hh
  rw [inner_gradient_left]
  linarith

theorem square_error (r s D : ℝ) (_hD : 0 ≤ D) (h : |r-s| ≤ D) :
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
open MeasureTheory ProbabilityTheory _root_.RandomGradFree.Shared _root_.AcceleratedSource.OracleMoment.RandomGradFree.Smooth

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


open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem aux_sgl_fderiv_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x : E) :
    fderiv ℝ f x = InnerProductSpace.toDual ℝ E (gradient f x) := by
  simp [gradient]

theorem aux_sgl_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x₀ : E) :
    Integrable (fun u => fderiv ℝ f (x₀ + μ • u)) (stdGaussian E) ∧
    HasFDerivAt (RandomGradFree.Shared.smoothing f μ)
      (∫ u, fderiv ℝ f (x₀ + μ • u) ∂(stdGaussian E)) x₀ := by
  set γ := stdGaussian E with hγ
  set G := ‖fderiv ℝ f 0‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hfc : Continuous f := hdiff.continuous
  have hcont : Continuous (fderiv ℝ f) := by
    refine (LipschitzWith.of_dist_le_mul (K := L₁.toNNReal) fun a b => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL₁]
    exact hL a b
  have hfd : ∀ z, ‖fderiv ℝ f z‖ ≤ G + L₁ * ‖z‖ := by
    intro z
    have := hL z 0
    simp only [sub_zero] at this
    have h2 := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f 0)
    linarith
  have hfb : ∀ z, ‖f z‖ ≤ ‖f 0‖ + (G + L₁ * ‖z‖) * ‖z‖ := by
    intro z
    have h := (convex_closedBall (0:E) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
      (f := f) (C := G + L₁ * ‖z‖) (x := 0) (y := z) (fun w _ => hdiff w)
      (fun w hw => by
        have := hfd w
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        nlinarith)
      (Metric.mem_closedBall_self (norm_nonneg z)) (by simp)
    simp only [sub_zero] at h
    have h2 := norm_sub_norm_le (f z) (f 0)
    linarith
  have hint1 : Integrable (fun u : E => ‖u‖) γ := IsGaussian.integrable_id.norm
  have hint2 : Integrable (fun u : E => ‖u‖ ^ 2) γ := by
    have := IsGaussian.memLp_id γ ((2 : ℕ) : ENNReal) (by simp)
    exact this.integrable_norm_pow two_ne_zero
  -- integrability of the derivative
  have hF'int : ∀ x : E, Integrable (fun u => fderiv ℝ f (x + μ • u)) γ := by
    intro x
    refine Integrable.mono' ((integrable_const (G + L₁ * ‖x‖)).add (hint1.const_mul (L₁ * μ)))
      ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfd (x + μ • u)
    have h2 : ‖x + μ • u‖ ≤ ‖x‖ + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  refine ⟨hF'int x₀, ?_⟩
  show HasFDerivAt (fun x => ∫ u, f (x + μ • u) ∂γ) _ x₀
  have hF_int : Integrable (fun u => f (x₀ + μ • u)) γ := by
    refine Integrable.mono'
      (((integrable_const (‖f 0‖ + G * ‖x₀‖ + 2 * L₁ * ‖x₀‖ ^ 2)).add
        (hint1.const_mul (G * μ))).add (hint2.const_mul (2 * L₁ * μ ^ 2)))
      ((hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfb (x₀ + μ • u)
    have h2 : ‖x₀ + μ • u‖ ≤ ‖x₀‖ + μ * ‖u‖ := by
      calc ‖x₀ + μ • u‖ ≤ ‖x₀‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x₀‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    set n := ‖x₀ + μ • u‖
    set a := ‖x₀‖
    set t := ‖u‖
    have hn : 0 ≤ n := norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have ht : 0 ≤ t := norm_nonneg _
    have hs : 0 ≤ a + μ * t := by positivity
    have e1 : G * n ≤ G * (a + μ * t) := mul_le_mul_of_nonneg_left h2 hG0
    have e2 : n * n ≤ (a + μ * t) * (a + μ * t) := mul_le_mul h2 h2 hn hs
    have e3 : (a + μ * t) * (a + μ * t) ≤ 2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2 := by
      nlinarith [sq_nonneg (a - μ * t)]
    have e4 : L₁ * (n * n) ≤ L₁ * (2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left (e2.trans e3) hL₁
    nlinarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x u => f (x + μ • u)) (F' := fun x u => fderiv ℝ f (x + μ • u))
    (bound := fun u => G + L₁ * (‖x₀‖ + 1) + L₁ * μ * ‖u‖)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    hF_int
    ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u x hx => ?_)
    ((integrable_const _).add (hint1.const_mul (L₁ * μ)))
    (Filter.Eventually.of_forall fun u x _ => ?_)
  · have h1 := hfd (x + μ • u)
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have := norm_le_norm_add_norm_sub' x x₀
      calc ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
            have := norm_sub_norm_le x x₀
            linarith
        _ ≤ ‖x₀‖ + 1 := by linarith
    have h2 : ‖x + μ • u‖ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
        _ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  · exact (hasFDerivAt_comp_add_right (μ • u)).2 (hdiff _).hasFDerivAt

end RandomGradFree.Accelerated

open _root_.AcceleratedSource.OracleMoment.RandomGradFree.Accelerated
open MeasureTheory ProbabilityTheory


namespace RandomProof
open MeasureTheory ProbabilityTheory _root_.AcceleratedSource.OracleMoment.RandomGradFree.Accelerated _root_.RandomGradFree.Shared

theorem gradient_diff_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    ‖gradient (smoothing f μ) x-gradient f x‖^2 ≤ μ^2*L^2*(Module.finrank ℝ E:ℝ) := by
  have hfd : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ L*‖x-y‖ := by
    intro x y
    rw [aux_sgl_fderiv_eq f x,aux_sgl_fderiv_eq f y,←map_sub,LinearIsometryEquiv.norm_map]
    exact hgrad x y
  have hm := aux_sgl_main f L hL hd hfd μ hμ x
  let D := fun u : E => fderiv ℝ f (x+μ • u)-fderiv ℝ f x
  have hDi : Integrable D (stdGaussian E) := hm.1.sub (integrable_const _)
  have hDn (u : E) : ‖D u‖ ≤ L*μ*‖u‖ := by
    have hh := hfd (x+μ • u) x
    simpa [D,norm_smul,Real.norm_of_nonneg hμ,mul_assoc] using hh
  have hDs (u : E) : ‖D u‖^2 ≤ (L*μ)^2*‖u‖^2 := by
    have hh := mul_self_le_mul_self (norm_nonneg _) (hDn u)
    nlinarith [hh]
  have h2 : Integrable (fun u : E => ‖u‖^2) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (2:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  have hD2 : Integrable (fun u => ‖D u‖^2) (stdGaussian E) := by
    refine Integrable.mono' (h2.const_mul ((L*μ)^2)) (hDi.aestronglyMeasurable.norm.pow 2) ?_
    exact Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hDs u)
  have hc : ConvexOn ℝ Set.univ (fun z : E →L[ℝ] ℝ => ‖z‖^2) :=
    (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2)
  have hj := hc.map_integral_le (μ := stdGaussian E) (f := D)
    (by fun_prop) isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hDi hD2
  have hbound : ‖∫ u, D u ∂(stdGaussian E)‖^2 ≤ (L*μ)^2*(Module.finrank ℝ E:ℝ) := by
    calc
      _ ≤ ∫ u, ‖D u‖^2 ∂(stdGaussian E) := hj
      _ ≤ ∫ u, (L*μ)^2*‖u‖^2 ∂(stdGaussian E) :=
        integral_mono hD2 (h2.const_mul _) (fun u => hDs u)
      _ = _ := by rw [integral_const_mul,RandomGradFree.Smooth.aux_sa_sq]
  have hnorm : ‖gradient (smoothing f μ) x-gradient f x‖ = ‖∫ u, D u ∂(stdGaussian E)‖ := by
    rw [show (∫ u, D u ∂(stdGaussian E)) = (∫ u, fderiv ℝ f (x+μ • u) ∂(stdGaussian E))-fderiv ℝ f x by
      dsimp [D]; rw [integral_sub hm.1 (integrable_const _)]; simp]
    simp only [gradient,hm.2.fderiv,←map_sub,LinearIsometryEquiv.norm_map]
  rw [hnorm]
  nlinarith [hbound]

theorem accelerated_moment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    ∫ u, ‖oracle f μ x u‖^2 ∂(stdGaussian E) ≤
      4*((Module.finrank ℝ E:ℝ)+4)*‖gradient (smoothing f μ) x‖^2+
      3*μ^2*L^2*((Module.finrank ℝ E:ℝ)+4)^3 := by
  have hdif := gradient_diff_sq f L hL hd hgrad μ hμ.le x
  have hn : 0 ≤ (Module.finrank ℝ E:ℝ) := Nat.cast_nonneg _
  have hgn : ‖gradient f x‖ ≤ ‖gradient (smoothing f μ) x‖+‖gradient (smoothing f μ) x-gradient f x‖ := by
    have hh := norm_sub_le (gradient (smoothing f μ) x) (gradient (smoothing f μ) x-gradient f x)
    simpa only [sub_sub_cancel] using hh
  have hgn2 := mul_self_le_mul_self (norm_nonneg _) hgn
  have hg : ‖gradient f x‖^2 ≤ 2*‖gradient (smoothing f μ) x‖^2+2*μ^2*L^2*(Module.finrank ℝ E:ℝ) := by
    nlinarith [sq_nonneg (‖gradient (smoothing f μ) x‖-‖gradient (smoothing f μ) x-gradient f x‖)]
  have hh := integrate_point_bound (fun u => oracle f μ x u) f x (hd x) (μ^2/2*L^2)
    (oracle_point f L hL hd hgrad μ hμ x)
  have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*((Module.finrank ℝ E:ℝ)+4) by positivity)
  have hp : ((Module.finrank ℝ E:ℝ)^3+6*(Module.finrank ℝ E:ℝ)^2+8*(Module.finrank ℝ E:ℝ))/2+
      4*((Module.finrank ℝ E:ℝ)+4)*(Module.finrank ℝ E:ℝ) ≤ 3*((Module.finrank ℝ E:ℝ)+4)^3 := by
    nlinarith [pow_nonneg hn 3,sq_nonneg (Module.finrank ℝ E:ℝ)]
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ μ^2*L^2 by positivity)
  nlinarith

end RandomProof

namespace RandomGradFree.Accelerated

theorem accepted {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    ∫ u, ‖RandomGradFree.Shared.oracle f μ x u‖ ^ 2 ∂(stdGaussian E)
      ≤ 4 * ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient (RandomGradFree.Shared.smoothing f μ) x‖ ^ 2
        + 3 * μ ^ 2 * L₁ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 3 := by
  exact RandomProof.accelerated_moment f L₁ hL₁ hdiff hgrad μ hμ x

end RandomGradFree.Accelerated

end AcceleratedSource.OracleMoment

end

section

namespace AcceleratedSource.SmoothingGradient

-- Prove2me | solution 1 for RandomGradFree.Accelerated.smoothing_hasGradient
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:49:12.834985+00:00
-- url     : https://prove2.me/submissions/043eecfd-96e8-4ab9-bf62-35cf43e0215c


open MeasureTheory ProbabilityTheory
namespace RandomStein

lemma pdf_deriv (x : ℝ) : HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt (fun y : ℝ => -y^2/2) (-x) x := by
    convert! ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
    ring
  change HasDerivAt (fun y : ℝ => (Real.sqrt (2*Real.pi*1))⁻¹ * Real.exp (-(y-0)^2/(2*1)))
    (-x*((Real.sqrt (2*Real.pi*1))⁻¹ * Real.exp (-(x-0)^2/(2*1)))) x
  simp only [sub_zero,mul_one]
  convert! h.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1
  ring

lemma density_integrable (f : ℝ → ℝ) (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x*f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (Filter.Eventually.of_forall (fun x => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

lemma scalar (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x)
    (hf : Integrable f (gaussianReal 0 1)) (hg : Integrable g (gaussianReal 0 1))
    (hxf : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    ∫ x, g x ∂(gaussianReal 0 1) = ∫ x, x*f x ∂(gaussianReal 0 1) := by
  have h1 : Integrable (f * (fun x => -x*gaussianPDFReal 0 1 x)) := by
    convert! (density_integrable _ hxf).neg using 1
    ext x
    simp only [Pi.mul_apply,Pi.neg_apply]
    ring
  have h2 : Integrable (g * gaussianPDFReal 0 1) := by
    convert! density_integrable g hg using 1
    ext x
    simp [mul_comm]
  have h3 : Integrable (f * gaussianPDFReal 0 1) := by
    convert! density_integrable f hf using 1
    ext x
    simp [mul_comm]
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd x) (fun x _ => pdf_deriv x) h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul (by norm_num),
    integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  have heq : (fun x => f x*(-x*gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x*(x*f x))) := by ext x; ring
  rw [heq,integral_neg] at hh
  have heq2 : (fun x => g x*gaussianPDFReal 0 1 x) =
      (fun x => gaussianPDFReal 0 1 x*g x) := by ext x; ring
  rw [heq2] at hh
  linarith

end RandomStein

namespace RandomStein
open MeasureTheory ProbabilityTheory

lemma pi_scalar {n : ℕ} (i : Fin (n+1)) (F G : (Fin (n+1) → ℝ) → ℝ)
    (hd : ∀ y t, HasDerivAt (fun a => F (i.insertNth a y)) (G (i.insertNth t y)) t)
    (hF : Integrable F (Measure.pi fun _ => gaussianReal 0 1))
    (hG : Integrable G (Measure.pi fun _ => gaussianReal 0 1))
    (hiF : Integrable (fun z => z i*F z) (Measure.pi fun _ => gaussianReal 0 1)) :
    ∫ z, G z ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, z i*F z ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hFc := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  have hGc := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hG
  have hic := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hiF
  simp only [Function.comp_def] at hFc hGc hic
  rw [←he.integral_comp' G,←he.integral_comp' (fun z => z i*F z),
    integral_prod_symm _ hGc,integral_prod_symm _ hic]
  apply integral_congr_ae
  filter_upwards [hFc.prod_left_ae,hGc.prod_left_ae,hic.prod_left_ae] with y hf hg hi
  have hef (a : ℝ) : e.symm (a,y) = i.insertNth a y := rfl
  change Integrable (fun x : ℝ => (i.insertNth (α := fun _ => ℝ) x y) i*F (i.insertNth x y)) (gaussianReal 0 1) at hi
  change (∫ x, G (i.insertNth x y) ∂(gaussianReal 0 1)) =
    (∫ x : ℝ, (i.insertNth (α := fun _ => ℝ) x y) i*F (i.insertNth x y) ∂(gaussianReal 0 1))
  simp only [Fin.insertNth_apply_same] at hi ⊢
  exact scalar _ _ (hd y) hf hg hi

end RandomStein

namespace RandomStein
open MeasureTheory ProbabilityTheory

lemma basis_scalar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (b : OrthonormalBasis (Fin (n+1)) ℝ E) (i : Fin (n+1))
    (f : E → ℝ) (hd : Differentiable ℝ f)
    (hf : Integrable f (stdGaussian E))
    (hg : Integrable (fun u => fderiv ℝ f u (b i)) (stdGaussian E))
    (huf : Integrable (fun u => inner ℝ (b i) u*f u) (stdGaussian E)) :
    ∫ u, fderiv ℝ f u (b i) ∂(stdGaussian E) =
      ∫ u, inner ℝ (b i) u*f u ∂(stdGaussian E) := by
  classical
  let T := fun z : Fin (n+1) → ℝ => ∑ j, z j • b j
  have hT : Measurable T := by fun_prop
  have hmap : stdGaussian E = (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1).map T :=
    stdGaussian_eq_map_pi_orthonormalBasis b
  have hf' := hf
  have hg' := hg
  have huf' := huf
  rw [hmap] at hf' hg' huf'
  have hfc := hf'.comp_measurable hT
  have hgc := hg'.comp_measurable hT
  have huc := huf'.comp_measurable hT
  have hi (z : Fin (n+1) → ℝ) : inner ℝ (b i) (T z) = z i := by
    exact b.orthonormal.inner_right_fintype z i
  simp only [Function.comp_def,hi] at hfc hgc huc
  have hpath (y : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun a => f (T (i.insertNth a y))) (fderiv ℝ f (T (i.insertNth t y)) (b i)) t := by
    have heq (a : ℝ) : T (i.insertNth a y) = a • b i+∑ j, y j • b (i.succAbove j) := by
      dsimp [T]
      rw [Fin.sum_univ_succAbove _ i]
      simp
    have hh : HasDerivAt (fun a : ℝ => T (i.insertNth a y)) (b i) t := by
      simp_rw [heq]
      simpa using ((hasDerivAt_id t).smul_const (b i)).add_const (∑ j, y j • b (i.succAbove j))
    convert! (hd (T (i.insertNth t y))).hasFDerivAt.comp_hasDerivAt t hh using 1
  have hh := pi_scalar i (fun z => f (T z)) (fun z => fderiv ℝ f (T z) (b i)) hpath hfc hgc huc
  rw [hmap,integral_map hT.aemeasurable hg'.aestronglyMeasurable,
    integral_map hT.aemeasurable huf'.aestronglyMeasurable]
  simp only [hi]
  exact hh

end RandomStein

namespace RandomStein
open MeasureTheory ProbabilityTheory

lemma basis_scalar_any {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n)
    (f : E → ℝ) (hd : Differentiable ℝ f)
    (hf : Integrable f (stdGaussian E))
    (hg : Integrable (fun u => fderiv ℝ f u (b i)) (stdGaussian E))
    (huf : Integrable (fun u => inner ℝ (b i) u*f u) (stdGaussian E)) :
    ∫ u, fderiv ℝ f u (b i) ∂(stdGaussian E) =
      ∫ u, inner ℝ (b i) u*f u ∂(stdGaussian E) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact basis_scalar b i f hd hf hg huf

lemma vector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hd : Differentiable ℝ f)
    (hf : Integrable f (stdGaussian E))
    (hg : Integrable (fun u => fderiv ℝ f u) (stdGaussian E))
    (huf : Integrable (fun u => f u • u) (stdGaussian E)) :
    (InnerProductSpace.toDual ℝ E).symm (∫ u, fderiv ℝ f u ∂(stdGaussian E)) =
      ∫ u, f u • u ∂(stdGaussian E) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  apply InnerProductSpace.ext_inner_left_basis b.toBasis
  intro i
  have hh := basis_scalar_any b i f hd hf (hg.apply_continuousLinearMap (b i))
    (by simpa only [inner_smul_right,smul_eq_mul,mul_comm] using huf.const_inner (𝕜 := ℝ) (b i))
  have heq : inner ℝ (b i) ((InnerProductSpace.toDual ℝ E).symm (∫ u, fderiv ℝ f u ∂(stdGaussian E))) =
      (∫ u, fderiv ℝ f u ∂(stdGaussian E)) (b i) := by
    rw [real_inner_comm]
    exact congrArg (fun L : E →L[ℝ] ℝ => L (b i)) ((InnerProductSpace.toDual ℝ E).apply_symm_apply _)
  change inner ℝ (b i) _ = inner ℝ (b i) _
  rw [heq,ContinuousLinearMap.integral_apply hg,←integral_inner huf]
  simpa only [inner_smul_right,smul_eq_mul,mul_comm] using hh

end RandomStein


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

open _root_.AcceleratedSource.SmoothingGradient.RandomGradFree.Smooth
open MeasureTheory ProbabilityTheory



open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem aux_sgl_fderiv_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x : E) :
    fderiv ℝ f x = InnerProductSpace.toDual ℝ E (gradient f x) := by
  simp [gradient]

theorem aux_sgl_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x₀ : E) :
    Integrable (fun u => fderiv ℝ f (x₀ + μ • u)) (stdGaussian E) ∧
    HasFDerivAt (RandomGradFree.Shared.smoothing f μ)
      (∫ u, fderiv ℝ f (x₀ + μ • u) ∂(stdGaussian E)) x₀ := by
  set γ := stdGaussian E with hγ
  set G := ‖fderiv ℝ f 0‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hfc : Continuous f := hdiff.continuous
  have hcont : Continuous (fderiv ℝ f) := by
    refine (LipschitzWith.of_dist_le_mul (K := L₁.toNNReal) fun a b => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL₁]
    exact hL a b
  have hfd : ∀ z, ‖fderiv ℝ f z‖ ≤ G + L₁ * ‖z‖ := by
    intro z
    have := hL z 0
    simp only [sub_zero] at this
    have h2 := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f 0)
    linarith
  have hfb : ∀ z, ‖f z‖ ≤ ‖f 0‖ + (G + L₁ * ‖z‖) * ‖z‖ := by
    intro z
    have h := (convex_closedBall (0:E) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
      (f := f) (C := G + L₁ * ‖z‖) (x := 0) (y := z) (fun w _ => hdiff w)
      (fun w hw => by
        have := hfd w
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        nlinarith)
      (Metric.mem_closedBall_self (norm_nonneg z)) (by simp)
    simp only [sub_zero] at h
    have h2 := norm_sub_norm_le (f z) (f 0)
    linarith
  have hint1 : Integrable (fun u : E => ‖u‖) γ := IsGaussian.integrable_id.norm
  have hint2 : Integrable (fun u : E => ‖u‖ ^ 2) γ := by
    have := IsGaussian.memLp_id γ ((2 : ℕ) : ENNReal) (by simp)
    exact this.integrable_norm_pow two_ne_zero
  -- integrability of the derivative
  have hF'int : ∀ x : E, Integrable (fun u => fderiv ℝ f (x + μ • u)) γ := by
    intro x
    refine Integrable.mono' ((integrable_const (G + L₁ * ‖x‖)).add (hint1.const_mul (L₁ * μ)))
      ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfd (x + μ • u)
    have h2 : ‖x + μ • u‖ ≤ ‖x‖ + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  refine ⟨hF'int x₀, ?_⟩
  show HasFDerivAt (fun x => ∫ u, f (x + μ • u) ∂γ) _ x₀
  have hF_int : Integrable (fun u => f (x₀ + μ • u)) γ := by
    refine Integrable.mono'
      (((integrable_const (‖f 0‖ + G * ‖x₀‖ + 2 * L₁ * ‖x₀‖ ^ 2)).add
        (hint1.const_mul (G * μ))).add (hint2.const_mul (2 * L₁ * μ ^ 2)))
      ((hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfb (x₀ + μ • u)
    have h2 : ‖x₀ + μ • u‖ ≤ ‖x₀‖ + μ * ‖u‖ := by
      calc ‖x₀ + μ • u‖ ≤ ‖x₀‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x₀‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    set n := ‖x₀ + μ • u‖
    set a := ‖x₀‖
    set t := ‖u‖
    have hn : 0 ≤ n := norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have ht : 0 ≤ t := norm_nonneg _
    have hs : 0 ≤ a + μ * t := by positivity
    have e1 : G * n ≤ G * (a + μ * t) := mul_le_mul_of_nonneg_left h2 hG0
    have e2 : n * n ≤ (a + μ * t) * (a + μ * t) := mul_le_mul h2 h2 hn hs
    have e3 : (a + μ * t) * (a + μ * t) ≤ 2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2 := by
      nlinarith [sq_nonneg (a - μ * t)]
    have e4 : L₁ * (n * n) ≤ L₁ * (2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left (e2.trans e3) hL₁
    nlinarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x u => f (x + μ • u)) (F' := fun x u => fderiv ℝ f (x + μ • u))
    (bound := fun u => G + L₁ * (‖x₀‖ + 1) + L₁ * μ * ‖u‖)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    hF_int
    ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u x hx => ?_)
    ((integrable_const _).add (hint1.const_mul (L₁ * μ)))
    (Filter.Eventually.of_forall fun u x _ => ?_)
  · have h1 := hfd (x + μ • u)
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have := norm_le_norm_add_norm_sub' x x₀
      calc ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
            have := norm_sub_norm_le x x₀
            linarith
        _ ≤ ‖x₀‖ + 1 := by linarith
    have h2 : ‖x + μ • u‖ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
        _ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  · exact (hasFDerivAt_comp_add_right (μ • u)).2 (hdiff _).hasFDerivAt

end RandomGradFree.Accelerated

open _root_.AcceleratedSource.SmoothingGradient.RandomGradFree.Accelerated
open MeasureTheory ProbabilityTheory


namespace RandomStein
open MeasureTheory ProbabilityTheory _root_.AcceleratedSource.SmoothingGradient.RandomGradFree.Accelerated _root_.AcceleratedSource.SmoothingGradient.RandomGradFree.Smooth _root_.RandomGradFree.Shared

lemma smooth_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (_hL : 0 ≤ L) (hd : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (fun u => f (x+μ • u)) (stdGaussian E) ∧
    Integrable (fun u => f (x+μ • u) • u) (stdGaussian E) := by
  have h1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  have h2 : Integrable (fun u : E => ‖u‖^2) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (2:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  have h3 : Integrable (fun u : E => ‖u‖^3) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (3:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  have hc : Continuous (fun u => f (x+μ • u)) := hd.continuous.comp (by fun_prop)
  have hb (u : E) : ‖f (x+μ • u)‖ ≤ ‖f x‖+μ*‖gradient f x‖*‖u‖+L/2*μ^2*‖u‖^2 := by
    have hh := aux_sa_descent f L hd hgrad x (μ • u)
    rw [norm_smul,Real.norm_of_nonneg hμ,mul_pow] at hh
    have ht := abs_real_inner_le_norm (gradient f x) (μ • u)
    rw [norm_smul,Real.norm_of_nonneg hμ] at ht
    have hsum := norm_add_le (f x) (inner ℝ (gradient f x) (μ • u))
    have hrem := norm_sub_norm_le (f (x+μ • u)) (f x+inner ℝ (gradient f x) (μ • u))
    rw [Real.norm_eq_abs] at hrem
    have ha : |f (x+μ • u)-(f x+inner ℝ (gradient f x) (μ • u))| ≤ L/2*(μ^2*‖u‖^2) := by
      simpa only [sub_add_eq_sub_sub] using hh
    rw [Real.norm_eq_abs] at hsum
    simp only [Real.norm_eq_abs] at hsum hrem ⊢
    nlinarith [ha,ht,hsum,hrem]
  constructor
  · refine Integrable.mono' (((integrable_const ‖f x‖).add (h1.const_mul (μ*‖gradient f x‖))).add
      (h2.const_mul (L/2*μ^2))) hc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hb
  · refine Integrable.mono' (((h1.const_mul ‖f x‖).add (h2.const_mul (μ*‖gradient f x‖))).add
      (h3.const_mul (L/2*μ^2))) (hc.smul continuous_id).aestronglyMeasurable ?_
    filter_upwards [] with u
    rw [norm_smul]
    have hh := mul_le_mul_of_nonneg_right (hb u) (norm_nonneg u)
    dsimp only [Pi.add_apply]
    nlinarith

lemma smooth_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hd : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (smoothing f μ) (∫ u, oracle f μ x u ∂(stdGaussian E)) x := by
  have hfd : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ L*‖x-y‖ := by
    intro x y
    rw [aux_sgl_fderiv_eq f x,aux_sgl_fderiv_eq f y,←map_sub,LinearIsometryEquiv.norm_map]
    exact hgrad x y
  have hm := aux_sgl_main f L hL hd hfd μ hμ.le x
  have hi := smooth_integrable f L hL hd hgrad μ hμ.le x
  let F := fun u => f (x+μ • u)
  have hFder (u : E) : HasFDerivAt F (μ • fderiv ℝ f (x+μ • u)) u := by
    convert! (hd (x+μ • u)).hasFDerivAt.comp u (((hasFDerivAt_id u).const_smul μ).const_add x) using 1
    ext v
    simp
  have hFdeq : fderiv ℝ F = fun u => μ • fderiv ℝ f (x+μ • u) := funext (fun u => (hFder u).fderiv)
  have hFi : Integrable (fun u => fderiv ℝ F u) (stdGaussian E) := by rw [hFdeq]; exact hm.1.smul μ
  have hs := vector F (fun u => (hFder u).differentiableAt) hi.1 hFi hi.2
  rw [hFdeq,integral_smul,LinearIsometryEquiv.map_smul] at hs
  have horacle : (∫ u, oracle f μ x u ∂(stdGaussian E)) =
      μ⁻¹ • (∫ u, F u • u ∂(stdGaussian E)) := by
    have hid : Integrable (fun u : E => u) (stdGaussian E) := IsGaussian.integrable_id
    have hpoint (u : E) : oracle f μ x u = μ⁻¹ • (F u • u-f x • u) := by
      simp only [oracle,if_neg hμ.ne',F,div_eq_mul_inv,smul_sub,smul_smul]
      rw [←sub_smul]
      congr 1
      ring
    simp_rw [hpoint]
    have hfu : Integrable (fun u => F u • u) (stdGaussian E) := hi.2
    have hconst : Integrable (fun u : E => f x • u) (stdGaussian E) := hid.smul (f x)
    rw [integral_smul,integral_sub hfu hconst,integral_smul,integral_id_stdGaussian]
    simp
  rw [horacle,←hs,smul_smul,inv_mul_cancel₀ hμ.ne',one_smul]
  exact hasGradientAt_iff_hasFDerivAt.mpr (by simpa using hm.2)

end RandomStein

namespace RandomGradFree.Accelerated

theorem accepted {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (RandomGradFree.Shared.smoothing f μ) (∫ u, RandomGradFree.Shared.oracle f μ x u ∂(stdGaussian E)) x := by
  exact RandomStein.smooth_identity f L₁ hL₁ hdiff hgrad μ hμ x

end RandomGradFree.Accelerated

end AcceleratedSource.SmoothingGradient

end

section

namespace AcceleratedSource.GradientLipschitz

-- Prove2me | solution 1 for RandomGradFree.Accelerated.smoothing_gradient_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:50:30.232977+00:00
-- url     : https://prove2.me/submissions/b24fdf89-955c-41c7-9ed7-7d088b64081d


open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem aux_sgl_fderiv_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x : E) :
    fderiv ℝ f x = InnerProductSpace.toDual ℝ E (gradient f x) := by
  simp [gradient]

theorem aux_sgl_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x₀ : E) :
    Integrable (fun u => fderiv ℝ f (x₀ + μ • u)) (stdGaussian E) ∧
    HasFDerivAt (RandomGradFree.Shared.smoothing f μ)
      (∫ u, fderiv ℝ f (x₀ + μ • u) ∂(stdGaussian E)) x₀ := by
  set γ := stdGaussian E with hγ
  set G := ‖fderiv ℝ f 0‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hfc : Continuous f := hdiff.continuous
  have hcont : Continuous (fderiv ℝ f) := by
    refine (LipschitzWith.of_dist_le_mul (K := L₁.toNNReal) fun a b => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL₁]
    exact hL a b
  have hfd : ∀ z, ‖fderiv ℝ f z‖ ≤ G + L₁ * ‖z‖ := by
    intro z
    have := hL z 0
    simp only [sub_zero] at this
    have h2 := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f 0)
    linarith
  have hfb : ∀ z, ‖f z‖ ≤ ‖f 0‖ + (G + L₁ * ‖z‖) * ‖z‖ := by
    intro z
    have h := (convex_closedBall (0:E) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
      (f := f) (C := G + L₁ * ‖z‖) (x := 0) (y := z) (fun w _ => hdiff w)
      (fun w hw => by
        have := hfd w
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        nlinarith)
      (Metric.mem_closedBall_self (norm_nonneg z)) (by simp)
    simp only [sub_zero] at h
    have h2 := norm_sub_norm_le (f z) (f 0)
    linarith
  have hint1 : Integrable (fun u : E => ‖u‖) γ := IsGaussian.integrable_id.norm
  have hint2 : Integrable (fun u : E => ‖u‖ ^ 2) γ := by
    have := IsGaussian.memLp_id γ ((2 : ℕ) : ENNReal) (by simp)
    exact this.integrable_norm_pow two_ne_zero
  -- integrability of the derivative
  have hF'int : ∀ x : E, Integrable (fun u => fderiv ℝ f (x + μ • u)) γ := by
    intro x
    refine Integrable.mono' ((integrable_const (G + L₁ * ‖x‖)).add (hint1.const_mul (L₁ * μ)))
      ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfd (x + μ • u)
    have h2 : ‖x + μ • u‖ ≤ ‖x‖ + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  refine ⟨hF'int x₀, ?_⟩
  show HasFDerivAt (fun x => ∫ u, f (x + μ • u) ∂γ) _ x₀
  have hF_int : Integrable (fun u => f (x₀ + μ • u)) γ := by
    refine Integrable.mono'
      (((integrable_const (‖f 0‖ + G * ‖x₀‖ + 2 * L₁ * ‖x₀‖ ^ 2)).add
        (hint1.const_mul (G * μ))).add (hint2.const_mul (2 * L₁ * μ ^ 2)))
      ((hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfb (x₀ + μ • u)
    have h2 : ‖x₀ + μ • u‖ ≤ ‖x₀‖ + μ * ‖u‖ := by
      calc ‖x₀ + μ • u‖ ≤ ‖x₀‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x₀‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    set n := ‖x₀ + μ • u‖
    set a := ‖x₀‖
    set t := ‖u‖
    have hn : 0 ≤ n := norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have ht : 0 ≤ t := norm_nonneg _
    have hs : 0 ≤ a + μ * t := by positivity
    have e1 : G * n ≤ G * (a + μ * t) := mul_le_mul_of_nonneg_left h2 hG0
    have e2 : n * n ≤ (a + μ * t) * (a + μ * t) := mul_le_mul h2 h2 hn hs
    have e3 : (a + μ * t) * (a + μ * t) ≤ 2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2 := by
      nlinarith [sq_nonneg (a - μ * t)]
    have e4 : L₁ * (n * n) ≤ L₁ * (2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left (e2.trans e3) hL₁
    nlinarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x u => f (x + μ • u)) (F' := fun x u => fderiv ℝ f (x + μ • u))
    (bound := fun u => G + L₁ * (‖x₀‖ + 1) + L₁ * μ * ‖u‖)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    hF_int
    ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u x hx => ?_)
    ((integrable_const _).add (hint1.const_mul (L₁ * μ)))
    (Filter.Eventually.of_forall fun u x _ => ?_)
  · have h1 := hfd (x + μ • u)
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have := norm_le_norm_add_norm_sub' x x₀
      calc ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
            have := norm_sub_norm_le x x₀
            linarith
        _ ≤ ‖x₀‖ + 1 := by linarith
    have h2 : ‖x + μ • u‖ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
        _ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  · exact (hasFDerivAt_comp_add_right (μ • u)).2 (hdiff _).hasFDerivAt

end RandomGradFree.Accelerated

open _root_.AcceleratedSource.GradientLipschitz.RandomGradFree.Accelerated
open MeasureTheory ProbabilityTheory

theorem accepted {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    Differentiable ℝ (RandomGradFree.Shared.smoothing f μ) ∧
      ∀ x y, ‖gradient (RandomGradFree.Shared.smoothing f μ) x - gradient (RandomGradFree.Shared.smoothing f μ) y‖ ≤ L₁ * ‖x - y‖ := by
  have hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L₁ * ‖x - y‖ := by
    intro x y
    rw [aux_sgl_fderiv_eq f x, aux_sgl_fderiv_eq f y, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact hgrad x y
  have hmain := aux_sgl_main f L₁ hL₁ hdiff hL μ hμ
  refine ⟨fun x => (hmain x).2.differentiableAt, fun x y => ?_⟩
  have hgx : gradient (RandomGradFree.Shared.smoothing f μ) x =
      (InnerProductSpace.toDual ℝ E).symm
        (∫ u, fderiv ℝ f (x + μ • u) ∂(stdGaussian E)) := by
    simp only [gradient, (hmain x).2.fderiv]
  have hgy : gradient (RandomGradFree.Shared.smoothing f μ) y =
      (InnerProductSpace.toDual ℝ E).symm
        (∫ u, fderiv ℝ f (y + μ • u) ∂(stdGaussian E)) := by
    simp only [gradient, (hmain y).2.fderiv]
  rw [hgx, hgy, ← map_sub, LinearIsometryEquiv.norm_map,
    ← integral_sub (hmain x).1 (hmain y).1]
  have := norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (f := fun u => fderiv ℝ f (x + μ • u) - fderiv ℝ f (y + μ • u)) (C := L₁ * ‖x - y‖)
    (Filter.Eventually.of_forall fun u => by
      have := hL (x + μ • u) (y + μ • u)
      simpa using this)
  simpa using this

end AcceleratedSource.GradientLipschitz

end

section

namespace AcceleratedSource.SmoothingApprox

-- Prove2me | solution 1 for RandomGradFree.Accelerated.smoothing_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:44:17.191434+00:00
-- url     : https://prove2.me/submissions/a9c0e632-eda9-4ef2-a8d2-515ac6c76d24


open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

open scoped RealInnerProductSpace in
theorem aux_sa_second_moment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hmem : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hint : ∀ i, Integrable (fun u : E => ⟪b i, u⟫ ^ 2) (stdGaussian E) := by
    intro i
    have := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ (b i)) 2 (by simp)
    simpa using this.integrable_sq
  have h1 : ∀ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h := covarianceBilin_apply (μ := stdGaussian E) hmem (b i) (b i)
    rw [covarianceBilin_stdGaussian, show (∫ x, id x ∂(stdGaussian E)) = 0 from integral_id_stdGaussian] at h
    simp only [sub_zero] at h
    have e : (innerSL ℝ (b i)) (b i) = 1 := by
      simp [b.orthonormal.1 i]
    rw [e] at h
    rw [h]
    congr 1
    ext u
    ring
  calc ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = ∫ u, ∑ i, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := by
        congr 1; ext u; rw [b.sum_sq_inner_right]
    _ = ∑ i, ∫ u, ⟪b i, u⟫ ^ 2 ∂(stdGaussian E) := integral_finsetSum _ (fun i _ => hint i)
    _ = Module.finrank ℝ E := by simp [h1]


open scoped RealInnerProductSpace in
theorem aux_sa_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖) (x h : E) :
    |f (x + h) - f x - ⟪gradient f x, h⟫| ≤ L₁ / 2 * ‖h‖ ^ 2 := by
  set φ : ℝ → ℝ := fun t => f (x + t • h) - f x - t * ⟪gradient f x, h⟫ with hφ
  have hderiv : ∀ t : ℝ, HasDerivAt φ (⟪gradient f (x + t • h), h⟫ - ⟪gradient f x, h⟫) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => x + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f (x + t • h))) (x + t • h) :=
      (hdiff _).hasGradientAt.hasFDerivAt
    have h3 := h2.comp_hasDerivAt t h1
    have h4 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, h⟫) ⟪gradient f x, h⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, h⟫
    have h5 := (h3.sub_const (f x)).sub h4
    exact h5
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := φ)
    (f' := fun t => ⟪gradient f (x + t • h), h⟫ - ⟪gradient f x, h⟫)
    (B := fun t => L₁ / 2 * t ^ 2 * ‖h‖ ^ 2) (B' := fun t => L₁ * t * ‖h‖ ^ 2)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (by simp [hφ])
    (by
      intro t
      have := ((hasDerivAt_pow 2 t).const_mul (L₁ / 2)).mul_const (‖h‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    (by
      intro t ht
      rw [← inner_sub_left, Real.norm_eq_abs]
      calc |⟪gradient f (x + t • h) - gradient f x, h⟫|
          ≤ ‖gradient f (x + t • h) - gradient f x‖ * ‖h‖ := abs_real_inner_le_norm _ _
        _ ≤ (L₁ * ‖(x + t • h) - x‖) * ‖h‖ := by
            gcongr; exact hgrad _ _
        _ = L₁ * t * ‖h‖ ^ 2 := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]; ring)
  have := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simpa [hφ, Real.norm_eq_abs] using this

open scoped RealInnerProductSpace in
theorem aux_sa_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (_hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (_hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ ^ 2 / 2 * L₁ * Module.finrank ℝ E := by
  set g := gradient f x with hg
  have hcont : Continuous f := hdiff.continuous
  set R : E → ℝ := fun u => f (x + μ • u) - f x - ⟪g, μ • u⟫ with hRdef
  have hR : ∀ u, |R u| ≤ L₁ / 2 * μ ^ 2 * ‖u‖ ^ 2 := by
    intro u
    have := aux_sa_descent f L₁ hdiff hgrad x (μ • u)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at this
    simp only [hRdef]
    linarith
  have hsq : Integrable (fun u : E => ‖u‖ ^ 2) (stdGaussian E) := by
    have h2 : MemLp id ((2 : ℕ) : ENNReal) (stdGaussian E) := by
      simpa using (IsGaussian.memLp_two_id (μ := stdGaussian E))
    simpa using h2.integrable_norm_pow (by norm_num)
  have hRcont : Continuous R := by
    simp only [hRdef]
    fun_prop
  have hRint : Integrable R (stdGaussian E) := by
    refine Integrable.mono' (hsq.const_mul (L₁ / 2 * μ ^ 2)) hRcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun u => by rw [Real.norm_eq_abs]; exact hR u)
  have hid : Integrable (fun u : E => μ • u) (stdGaussian E) :=
    (IsGaussian.integrable_id (μ := stdGaussian E)).smul μ
  have hlin : Integrable (fun u : E => ⟪g, μ • u⟫) (stdGaussian E) := hid.const_inner g
  have hlin0 : ∫ u, ⟪g, μ • u⟫ ∂(stdGaussian E) = 0 := by
    rw [integral_inner hid, integral_smul, integral_id_stdGaussian]
    simp
  have hsplit : RandomGradFree.Shared.smoothing f μ x - f x = ∫ u, R u ∂(stdGaussian E) := by
    unfold RandomGradFree.Shared.smoothing
    have e : ∀ u, f (x + μ • u) = (R u + f x) + ⟪g, μ • u⟫ := by
      intro u; simp only [hRdef]; ring
    simp_rw [e]
    have hRc : Integrable (fun u => R u + f x) (stdGaussian E) := hRint.add (integrable_const _)
    rw [integral_add hRc hlin, integral_add hRint (integrable_const _), integral_const, hlin0]
    simp
  rw [hsplit]
  calc |∫ u, R u ∂(stdGaussian E)| ≤ ∫ u, |R u| ∂(stdGaussian E) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, L₁ / 2 * μ ^ 2 * ‖u‖ ^ 2 ∂(stdGaussian E) :=
        integral_mono hRint.abs (hsq.const_mul _) hR
    _ = L₁ / 2 * μ ^ 2 * Module.finrank ℝ E := by
        rw [integral_const_mul, aux_sa_second_moment]
    _ = μ ^ 2 / 2 * L₁ * Module.finrank ℝ E := by ring

end RandomGradFree.Accelerated

open _root_.AcceleratedSource.SmoothingApprox.RandomGradFree.Accelerated
open MeasureTheory ProbabilityTheory

theorem accepted {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ ^ 2 / 2 * L₁ * Module.finrank ℝ E :=
  aux_sa_main f L₁ hL₁ hdiff hgrad μ hμ x

end AcceleratedSource.SmoothingApprox

end

section

namespace AcceleratedSource.SmoothingJensen

-- Prove2me | solution 1 for RandomGradFree.Accelerated.le_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:40:28.490367+00:00
-- url     : https://prove2.me/submissions/1c93b1f6-0de5-4f5e-829c-a49c45c7f76c


open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem aux_acclesm_integrable_id {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Integrable (fun u : E => u) (stdGaussian E) :=
  IsGaussian.integrable_id

end RandomGradFree.Accelerated

open _root_.AcceleratedSource.SmoothingJensen.RandomGradFree.Accelerated

theorem accepted {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (_hμ : 0 ≤ μ) (x : E)
    (hint : Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    f x ≤ RandomGradFree.Shared.smoothing f μ x := by
  have hcont : ContinuousOn f Set.univ := hf.continuousOn isOpen_univ
  have hid : Integrable (fun u : E => u) (stdGaussian E) := aux_acclesm_integrable_id
  have hg : Integrable (fun u : E => x + μ • u) (stdGaussian E) :=
    (integrable_const x).add (hid.smul μ)
  have hJ := hf.map_integral_le (μ := stdGaussian E) (f := fun u : E => x + μ • u) hcont
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hg hint
  have hmean : ∫ u, (x + μ • u) ∂(stdGaussian E) = x := by
    have hs : Integrable (fun u : E => μ • u) (stdGaussian E) := hid.smul μ
    rw [integral_add (integrable_const x) hs, integral_const, integral_smul,
      integral_id_stdGaussian]
    simp
  rw [hmean] at hJ
  simpa [RandomGradFree.Shared.smoothing] using hJ

end AcceleratedSource.SmoothingJensen

end

section

namespace AcceleratedSource.DirectionalMean

-- Prove2me | solution 1 for RandomGradFree.Smooth.directional_oracle_mean
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:27:27.761193+00:00
-- url     : https://prove2.me/submissions/aa647048-f2f2-4428-891b-c725f0dc4807


open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

open scoped RealInnerProductSpace in
theorem aux_dom_cov_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (g y : E) :
    ⟪covarianceOperator (stdGaussian E) g, y⟫ = ⟪g, y⟫ := by
  have hμ : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  rw [covarianceOperator_inner hμ]
  have h := covarianceBilin_apply hμ g y
  rw [covarianceBilin_stdGaussian] at h
  have h0 : ∫ z, id z ∂(stdGaussian E) = 0 := integral_id_stdGaussian
  simp only [h0, sub_zero] at h
  rw [← h]
  exact innerSL_apply_apply ℝ g y

end RandomGradFree.Smooth

open _root_.AcceleratedSource.DirectionalMean.RandomGradFree.Smooth
open MeasureTheory ProbabilityTheory

theorem accepted {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) (_hfx : DifferentiableAt ℝ f x) :
    ∫ u, fderiv ℝ f x u • u ∂(stdGaussian E) = gradient f x := by
  have hμ : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hL : ∀ u, fderiv ℝ f x u = inner ℝ (gradient f x) u := by
    intro u
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  simp_rw [hL]
  rw [← covarianceOperator_apply hμ]
  refine ext_inner_right ℝ fun y => ?_
  exact aux_dom_cov_inner _ _

end AcceleratedSource.DirectionalMean

end

section

-- Prove2me | solution 1 for RandomGradFree.Smooth.random_gradient_method_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:44:55.030494+00:00
-- url     : https://prove2.me/submissions/9bae62cb-8ff0-44e7-aa81-07d2d1096a03


set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace RG33

section analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inner_grad (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma line_deriv {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [inner_grad]
  exact this

lemma descent {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hdiff x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, w⟫) ⟪gradient f x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ =
        ⟪gradient f (x + c • w) - gradient f x, w⟫ := by rw [inner_sub_left]
    have e2 := real_inner_le_norm (gradient f (x + c • w) - gradient f x) w
    have e3 := hgrad (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖gradient f (x + c • w) - gradient f x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

lemma convex_fo {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f) (x y : E) :
    f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • w)) := by
    have := hf.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => f (x + t • w)) = f ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using line_deriv hdiff x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  rw [inner_grad]
  linarith

lemma grad_sq_le {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) {xstar : E}
    (hopt : ∀ y, f xstar ≤ f y) (x : E) :
    ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - f xstar) := by
  have h := descent hdiff hgrad x (x - (1 / L) • gradient f x)
  have h2 := hopt (x - (1 / L) • gradient f x)
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  have : L / 2 * (1 / L * ‖gradient f x‖) ^ 2 = 1 / (2 * L) * ‖gradient f x‖ ^ 2 := by
    field_simp
  rw [this] at h
  have h3 : 1 / L * ‖gradient f x‖ ^ 2 - 1 / (2 * L) * ‖gradient f x‖ ^ 2 ≤ f x - f xstar := by
    linarith
  have h4 : 1 / L * ‖gradient f x‖ ^ 2 - 1 / (2 * L) * ‖gradient f x‖ ^ 2 =
      ‖gradient f x‖ ^ 2 / (2 * L) := by field_simp; ring
  rw [h4, div_le_iff₀ (by positivity)] at h3
  linarith

lemma grad_star {f : E → ℝ} {L : ℝ} (hL : 0 < L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) {xstar : E}
    (hopt : ∀ y, f xstar ≤ f y) : gradient f xstar = 0 := by
  have := grad_sq_le hL hdiff hgrad hopt xstar
  rw [sub_self, mul_zero] at this
  have h0 : ‖gradient f xstar‖ = 0 := by nlinarith [norm_nonneg (gradient f xstar)]
  exact norm_eq_zero.mp h0

lemma grad_cont {f : E → ℝ} {L : ℝ} (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    Continuous (gradient f) := by
  have : LipschitzWith (Real.toNNReal L) (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    refine (hgrad x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
  exact this.continuous

end analysis

section core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- scalar coefficient of the oracle -/
noncomputable def coef (f : E → ℝ) (μ : ℝ) (y v : E) : ℝ :=
  if μ = 0 then ⟪gradient f y, v⟫ else (f (y + μ • v) - f y) / μ

variable {f : E → ℝ} {L μ : ℝ}

lemma coef_bounds (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hf : ConvexOn ℝ Set.univ f) (hμ : 0 ≤ μ) (y v : E) :
    ⟪gradient f y, v⟫ ≤ coef f μ y v ∧
      coef f μ y v ≤ ⟪gradient f y, v⟫ + L * μ / 2 * ‖v‖ ^ 2 := by
  unfold coef
  split_ifs with h0
  · subst h0; simp
  · have hμp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm h0)
    have h1 := convex_fo hf hdiff y (y + μ • v)
    have h2 := descent hdiff hgrad y (y + μ • v)
    rw [add_sub_cancel_left, real_inner_smul_right] at h1 h2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμp] at h2
    constructor
    · rw [le_div_iff₀ hμp]; linarith
    · rw [div_le_iff₀ hμp]
      have e : (⟪gradient f y, v⟫ + L * μ / 2 * ‖v‖ ^ 2) * μ =
          μ * ⟪gradient f y, v⟫ + L / 2 * (μ * ‖v‖) ^ 2 := by ring
      rw [e]; linarith

lemma coef_cont_joint (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    Continuous (fun p : E × E => coef f μ p.1 p.2) := by
  unfold coef
  split_ifs with h0
  · exact ((grad_cont hgrad).comp continuous_fst).inner continuous_snd
  · have hc := hdiff.continuous
    fun_prop

lemma coef_cont (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (y : E) :
    Continuous (coef f μ y) :=
  (coef_cont_joint (μ := μ) hdiff hgrad).comp (continuous_const.prodMk continuous_id)


end core

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma oracle_eq {f : E → ℝ} {μ : ℝ} (hdiff : Differentiable ℝ f) (y v : E) :
    RandomGradFree.Shared.oracle f μ y v = coef f μ y v • v := by
  unfold RandomGradFree.Shared.oracle coef
  split_ifs with h0
  · congr 1
    have hd := line_deriv hdiff y v 0
    rw [zero_smul, add_zero] at hd
    have ht := hasDerivAt_iff_tendsto_slope_zero.mp hd
    have ht2 : Filter.Tendsto (fun α : ℝ => (f (y + α • v) - f y) / α)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪gradient f y, v⟫) := by
      refine (ht.mono_left (nhdsWithin_mono _ ?_)).congr ?_
      · intro t (htt : 0 < t); exact htt.ne'
      · intro t; simp only [zero_add, zero_smul, add_zero, smul_eq_mul]; rw [div_eq_inv_mul]
    exact ht2.limUnder_eq
  · rfl


end
end RG33

end

section

namespace AcceleratedSource.PsiLinear

-- Prove2me | solution 1 for RandomGradFree.Accelerated.psi_bound_linear
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:58:09.523993+00:00
-- url     : https://prove2.me/submissions/f4a2b2cb-e512-43b1-b8d2-3f27d462621a

open _root_.RandomGradFree.Accelerated
open scoped BigOperators

theorem accepted (α : ℕ → ℝ) (n : ℕ) (κ : ℝ)
    (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (_hκ : 0 ≤ κ) (_hκ1 : κ ≤ 1)
    (hακ : ∀ j, Real.sqrt κ / (4 * ((n : ℝ) + 4)) ≤ α j)
    (k : ℕ) :
    psi α k ≤ (1 - Real.sqrt κ / (4 * ((n : ℝ) + 4))) ^ k := by
  unfold psi
  calc
    (∏ i ∈ Finset.range k, (1-α i)) ≤ ∏ i ∈ Finset.range k, (1-Real.sqrt κ/(4*((n:ℝ)+4))) :=
      Finset.prod_le_prod (fun i hi => sub_nonneg.mpr (hα i).2) (fun i hi => by linarith [hακ i])
    _ = _ := by simp

end AcceleratedSource.PsiLinear

end

section

namespace AcceleratedSource.CLinear

-- Prove2me | solution 1 for RandomGradFree.Accelerated.c_bound_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:57:59.829911+00:00
-- url     : https://prove2.me/submissions/df8c681b-9da8-46bb-a2b0-870dd58310cf

open _root_.RandomGradFree.Accelerated
open scoped BigOperators

theorem accepted (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1) (k : ℕ) :
    C α k ≤ (k : ℝ) := by
  classical
  by_cases hk : k=0
  · simp [C,hk]
  · have hprod (i : ℕ) : (∏ j ∈ Finset.Ico (k-i) k, (1-α j)) ≤ 1 :=
      Finset.prod_le_one (fun j hj => sub_nonneg.mpr (hα j).2) (fun j hj => by linarith [(hα j).1])
    have hs := Finset.sum_le_sum (fun i (hi : i∈Finset.Ico 1 k) => hprod i)
    rw [C,if_neg hk]
    calc
      1+(∑ i ∈ Finset.Ico 1 k, ∏ j ∈ Finset.Ico (k-i) k, (1-α j)) ≤ 1+∑ i ∈ Finset.Ico 1 k, (1 : ℝ) := by linarith
      _ = k := by simp; rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num

end AcceleratedSource.CLinear

end

section

namespace AcceleratedSource.CStrong

-- Prove2me | solution 1 for RandomGradFree.Accelerated.c_bound_strongly_convex
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:19:20.097674+00:00
-- url     : https://prove2.me/submissions/14f1f1ca-bc8f-4c7b-914d-6eebcc132c3d

open _root_.RandomGradFree.Accelerated
open scoped BigOperators

theorem accepted (n : ℕ) (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1)
    (τ : ℝ) (hτ : 0 < τ) (L₁ : ℝ) (hL₁ : 0 < L₁)
    (hακ : ∀ j, Real.sqrt (τ / L₁) / (4 * ((n : ℝ) + 4)) ≤ α j)
    (k : ℕ) : C α k ≤ 4 * ((n : ℝ) + 4) / Real.sqrt (τ / L₁) := by
  let a:=Real.sqrt (τ/L₁)/(4*((n:ℝ)+4))
  let q:=1-a
  let K:=4*((n:ℝ)+4)/Real.sqrt (τ/L₁)
  have hsqrt:0 < Real.sqrt (τ/L₁):=Real.sqrt_pos.2 (div_pos hτ hL₁)
  have hden:0 < 4*((n:ℝ)+4):=by positivity
  have ha:0 < a:=div_pos hsqrt hden
  have ha1:a ≤ 1:=(hακ 0).trans (hα 0).2
  have hq:0 ≤ q:=sub_nonneg.mpr ha1
  have hK:0 < K:=div_pos hden hsqrt
  have hKa:a*K=1:=by dsimp [a,K];field_simp
  have hsum:(∑ i∈Finset.range k,q^i) ≤ K := by
    have he:=geom_sum_mul q k
    have he' : a*(∑ i∈Finset.range k,q^i)=1-q^k := by dsimp [q] at *;nlinarith
    have hp:=pow_nonneg hq k
    nlinarith
  by_cases hk:k=0
  · subst k;simpa [C] using hK.le
  · have hprod (i : ℕ) (hi : i∈Finset.Ico 1 k) :
        (∏ j∈Finset.Ico (k-i) k,(1-α j)) ≤ q^i := by
      have hh:=Finset.prod_le_prod (fun j (_ : j∈Finset.Ico (k-i) k)=>sub_nonneg.mpr (hα j).2)
        (fun j (_ : j∈Finset.Ico (k-i) k)=>show 1-α j ≤ q from sub_le_sub_left (hακ j) 1)
      have hic:i ≤ k:=by have := (Finset.mem_Ico.mp hi).2;omega
      simpa [Finset.prod_const,Nat.card_Ico,Nat.sub_sub_self hic] using hh
    have hh:=Finset.sum_le_sum hprod
    have he:1+(∑ i∈Finset.Ico 1 k,q^i)=∑ i∈Finset.range k,q^i := by
      rw [Finset.sum_Ico_eq_sub (fun i=>q^i) (by omega : 1 ≤ k)]
      simp
    rw [C,if_neg hk]
    calc
      _ ≤ 1+∑ i∈Finset.Ico 1 k,q^i:=by linarith
      _ = ∑ i∈Finset.range k,q^i:=he
      _ ≤ K:=hsum

end AcceleratedSource.CStrong

end

end

/- Complete checked assembly: LCore -/
section

set_option autoImplicit false

/- Complete source body: CoefficientCore -/
section

set_option autoImplicit false

namespace RandomGradFree.AcceleratedProof

theorem coefficient_step {τ θ g gp a : ℝ}
    (hτ : 0 ≤ τ) (hθ : 0 < θ) (hθτ : θ * τ < 1)
    (hg : 0 < g) (hτg : τ ≤ g) (ha : 0 < a)
    (heq : a ^ 2 / θ = (1 - a) * g + a * τ)
    (hgp : gp = (1 - a) * g + a * τ) :
    a < 1 ∧ 0 < gp ∧ τ ≤ gp ∧ gp ≤ g := by
  have hs : a ^ 2 = θ * gp := by
    rw [← hgp] at heq
    exact ((div_eq_iff hθ.ne').mp heq).trans (mul_comm gp θ)
  have ha1 : a < 1 := by
    by_contra hn
    have h1 : 1 ≤ a := le_of_not_gt hn
    have hh : 0 ≤ (a - 1) * (g - τ) := mul_nonneg (by linarith) (by linarith)
    have hgpt : gp ≤ τ := by rw [hgp]; nlinarith
    have hlt : θ * gp < 1 := (mul_le_mul_of_nonneg_left hgpt hθ.le).trans_lt hθτ
    nlinarith
  refine ⟨ha1, ?_, ?_, ?_⟩
  · rw [hgp]
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hg) (mul_nonneg ha.le hτ)
  · rw [hgp]
    have := mul_nonneg (show 0 ≤ 1-a by linarith) (show 0 ≤ g-τ by linarith)
    nlinarith
  · rw [hgp]
    have := mul_nonneg ha.le (show 0 ≤ g-τ by linarith)
    nlinarith

theorem coefficient_gamma_bounds {τ θ : ℝ} (hτ : 0 ≤ τ) (hθ : 0 < θ)
    (hθτ : θ * τ < 1) (γ α : ℕ → ℝ)
    (hγ0 : 0 < γ 0) (hτγ0 : τ ≤ γ 0) (hα : ∀ k, 0 < α k)
    (heq : ∀ k, α k ^ 2 / θ = (1-α k)*γ k + α k*τ)
    (hγ : ∀ k, γ (k+1) = (1-α k)*γ k + α k*τ) :
    ∀ k, 0 < γ k ∧ τ ≤ γ k ∧ γ k ≤ γ 0 := by
  intro k
  induction k with
  | zero => exact ⟨hγ0, hτγ0, le_rfl⟩
  | succ k ih =>
    obtain ⟨_, hp, ht, hb⟩ := coefficient_step hτ hθ hθτ ih.1 ih.2.1
      (hα k) (heq k) (hγ k)
    exact ⟨hp, ht, hb.trans ih.2.2⟩

theorem coefficient_alpha_lt_one {τ θ : ℝ} (hτ : 0 ≤ τ) (hθ : 0 < θ)
    (hθτ : θ * τ < 1) (γ α : ℕ → ℝ)
    (hγ0 : 0 < γ 0) (hτγ0 : τ ≤ γ 0) (hα : ∀ k, 0 < α k)
    (heq : ∀ k, α k ^ 2 / θ = (1-α k)*γ k + α k*τ)
    (hγ : ∀ k, γ (k+1) = (1-α k)*γ k + α k*τ) (k : ℕ) : α k < 1 := by
  have hg := coefficient_gamma_bounds hτ hθ hθτ γ α hγ0 hτγ0 hα heq hγ k
  exact (coefficient_step hτ hθ hθτ hg.1 hg.2.1 (hα k) (heq k) (hγ k)).1

theorem coefficient_square {θ : ℝ} (hθ : θ ≠ 0) (γ α : ℕ → ℝ)
    (heq : ∀ k, α k ^ 2 / θ = γ (k+1)) (k : ℕ) :
    α k ^ 2 = θ * γ (k+1) := by
  exact ((div_eq_iff hθ).mp (heq k)).trans (mul_comm _ _)

end RandomGradFree.AcceleratedProof

end

/- Complete source body: StepParameters -/
section

set_option autoImplicit false

namespace RandomGradFree.AcceleratedProof

theorem tau_le_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 0 < Module.finrank ℝ E)
    (f : E → ℝ) (L τ : ℝ)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hsc : ∀ x y, f x+inner ℝ (gradient f x) (y-x)+τ/2*‖y-x‖^2 ≤ f y) :
    τ ≤ L := by
  obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  have h0 := hsc 0 u
  have h1 := hsc u 0
  simp only [sub_zero, zero_sub, inner_neg_right, norm_neg] at h0 h1
  have hi : τ*‖u‖^2 ≤ inner ℝ (gradient f u-gradient f 0) u := by
    rw [inner_sub_left]
    linarith
  have hb := (real_inner_le_norm (gradient f u-gradient f 0) u).trans
    (mul_le_mul_of_nonneg_right (hgrad u 0) (norm_nonneg u))
  simp only [sub_zero] at hb
  have hm : τ*‖u‖^2 ≤ L*‖u‖^2 := by nlinarith
  exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hu))).mp hm

theorem theta_pos_and_small {n L τ : ℝ} (hn : 0 ≤ n) (hL : 0 < L)
    (hτL : τ ≤ L) :
    0 < 1/(16*(n+4)^2*L) ∧ (1/(16*(n+4)^2*L))*τ < 1 := by
  have hn4 : 0 < n+4 := by linarith
  have hd : 0 < 16*(n+4)^2*L := by positivity
  refine ⟨by positivity, ?_⟩
  have hbase : 1 < 16*(n+4)^2 := by nlinarith
  have hlt : L < 16*(n+4)^2*L := by nlinarith
  have hh : τ/(16*(n+4)^2*L) < 1 := (div_lt_one hd).mpr (hτL.trans_lt hlt)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh

theorem step_parameter_cancellation {n L : ℝ} (hn : 0 ≤ n) (hL : 0 < L) :
    (1/(4*(n+4)*L))/(4*(n+4))-(1/(4*(n+4)*L))^2*L/2 =
      (1/(16*(n+4)^2*L))/2 := by
  have hn4 : n+4 ≠ 0 := by linarith
  field_simp
  ring

theorem scalar_bias_bound {n μ L : ℝ} (hn : 2 ≤ n) (hL : 0 ≤ L) :
    (1/(4*(n+4)*L))*(3*μ^2*L^2*(n+4)^3)/(4*(n+4)) ≤
      3*μ^2*L*(n+8)/16 := by
  by_cases hL0 : L=0
  · simp [hL0]
  have hn4 : n+4 ≠ 0 := by linarith
  have he : (1/(4*(n+4)*L))*(3*μ^2*L^2*(n+4)^3)/(4*(n+4)) =
      3*μ^2*L*(n+4)/16 := by field_simp; ring
  rw [he]
  have := mul_nonneg (sq_nonneg μ) hL
  nlinarith

theorem moment_to_descent {n μ L θ h Q G A B : ℝ} (hn : 2 ≤ n) (hL : 0 < L)
    (hθ : θ=1/(16*(n+4)^2*L)) (hh : h=1/(4*(n+4)*L))
    (hm : Q ≤ 4*(n+4)*G+3*μ^2*L^2*(n+4)^3)
    (hs : A ≤ B-h*G+h^2*L/2*Q) :
    A ≤ B-θ/2*Q+3*μ^2*L*(n+8)/16 := by
  have hn0 : 0 ≤ n := by linarith
  have hn4 : 0<n+4 := by linarith
  have hp : 0 ≤ h/(4*(n+4)) := by rw [hh]; positivity
  have hm' := mul_le_mul_of_nonneg_left hm hp
  have he : (h/(4*(n+4)))*(4*(n+4)*G+3*μ^2*L^2*(n+4)^3) =
      h*G+h*(3*μ^2*L^2*(n+4)^3)/(4*(n+4)) := by field_simp
  rw [he] at hm'
  have hb : h*(3*μ^2*L^2*(n+4)^3)/(4*(n+4)) ≤ 3*μ^2*L*(n+8)/16 := by
    rw [hh]
    exact scalar_bias_bound hn hL.le
  have hc : h/(4*(n+4))-h^2*L/2=θ/2 := by
    rw [hθ, hh]
    exact step_parameter_cancellation hn0 hL
  have hcQ := congrArg (fun t : ℝ => t*Q) hc
  nlinarith

end RandomGradFree.AcceleratedProof

end

/- Complete source body: GammaProduct -/
section

set_option autoImplicit false
open RandomGradFree.Accelerated

namespace RandomGradFree.AcceleratedProof

theorem psi_zero (α : ℕ → ℝ) : psi α 0 = 1 := by simp [psi]

theorem psi_succ (α : ℕ → ℝ) (k : ℕ) :
    psi α (k+1) = psi α k * (1-α k) := by simp [psi, Finset.prod_range_succ]

theorem psi_pos (α : ℕ → ℝ) (hα : ∀ k, α k < 1) (k : ℕ) : 0 < psi α k := by
  unfold psi
  exact Finset.prod_pos (fun i _ => sub_pos.mpr (hα i))

theorem psi_le_one (α : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k)
    (hα1 : ∀ k, α k ≤ 1) (k : ℕ) : psi α k ≤ 1 := by
  unfold psi
  exact Finset.prod_le_one (fun i _ => sub_nonneg.mpr (hα1 i))
    (fun i _ => by linarith [hα0 i])

theorem gamma_eq_tau_add_psi (τ : ℝ) (γ α : ℕ → ℝ)
    (hγ : ∀ k, γ (k+1) = (1-α k)*γ k + α k*τ) (k : ℕ) :
    γ k = τ + psi α k * (γ 0-τ) := by
  induction k with
  | zero => simp [psi_zero]
  | succ k ih => rw [hγ, ih, psi_succ]; ring

theorem psi_mul_gamma_zero_le (τ : ℝ) (hτ : 0 ≤ τ) (γ α : ℕ → ℝ)
    (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∀ k, α k ≤ 1)
    (hγ : ∀ k, γ (k+1) = (1-α k)*γ k + α k*τ) (k : ℕ) :
    psi α k * γ 0 ≤ γ k := by
  rw [gamma_eq_tau_add_psi τ γ α hγ k]
  have := mul_nonneg hτ (sub_nonneg.mpr (psi_le_one α hα0 hα1 k))
  nlinarith

theorem alpha_square_ge_psi (τ θ : ℝ) (hτ : 0 ≤ τ) (hθ : 0 ≤ θ)
    (γ α : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∀ k, α k ≤ 1)
    (hγ : ∀ k, γ (k+1) = (1-α k)*γ k + α k*τ)
    (hs : ∀ k, α k ^ 2 = θ * γ (k+1)) (k : ℕ) :
    (θ * γ 0) * psi α (k+1) ≤ α k ^ 2 := by
  rw [hs]
  have hh := mul_le_mul_of_nonneg_left
    (psi_mul_gamma_zero_le τ hτ γ α hα0 hα1 hγ (k+1)) hθ
  nlinarith

end RandomGradFree.AcceleratedProof

end

/- Complete source body: QuadraticProductRate -/
section

set_option autoImplicit false
open RandomGradFree.Accelerated

namespace RandomGradFree.AcceleratedProof

theorem inverse_progress {a b p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hqp : q ≤ p) (hs : q ^ 2 = (1-b)*p ^ 2) (ha : a*q ≤ b) :
    a/2 ≤ 1/q-1/p := by
  have hmul := mul_le_mul_of_nonneg_right ha (sq_nonneg p)
  have hgap := mul_nonneg (sub_nonneg.mpr hqp) (sub_nonneg.mpr hqp)
  have hnum : a*q*p ≤ 2*(p-q) := by
    apply (mul_le_mul_iff_of_pos_right hp).mp
    nlinarith
  calc
    a/2 ≤ (p-q)/(p*q) := by
      apply (le_div_iff₀ (mul_pos hp hq)).mpr
      nlinarith
    _ = 1/q-1/p := by field_simp

theorem psi_inverse_sqrt_progress (α : ℕ → ℝ) (hα0 : ∀ k, 0 < α k)
    (hα1 : ∀ k, α k < 1) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ k, a ^ 2 * psi α (k+1) ≤ α k ^ 2) (k : ℕ) :
    a/2 ≤ 1/Real.sqrt (psi α (k+1)) - 1/Real.sqrt (psi α k) := by
  have hp := psi_pos α hα1 k
  have hq := psi_pos α hα1 (k+1)
  have hps := Real.sq_sqrt hp.le
  have hqs := Real.sq_sqrt hq.le
  apply inverse_progress (b := α k) (Real.sqrt_pos.mpr hp) (Real.sqrt_pos.mpr hq)
  · apply Real.sqrt_le_sqrt
    rw [psi_succ]
    nlinarith [hα0 k]
  · rw [hps, hqs, psi_succ]
    ring
  · have h := hs k
    have hn : 0 ≤ a * Real.sqrt (psi α (k+1)) := mul_nonneg ha (Real.sqrt_nonneg _)
    have he : (a*Real.sqrt (psi α (k+1)))^2=a^2*psi α (k+1) := by rw [mul_pow, hqs]
    nlinarith [hα0 k]

theorem psi_inverse_sqrt_lower (α : ℕ → ℝ) (hα0 : ∀ k, 0 < α k)
    (hα1 : ∀ k, α k < 1) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ k, a ^ 2 * psi α (k+1) ≤ α k ^ 2) (k : ℕ) :
    1 + (k : ℝ)*a/2 ≤ 1/Real.sqrt (psi α k) := by
  induction k with
  | zero => simp [psi_zero]
  | succ k ih =>
    have hp := psi_inverse_sqrt_progress α hα0 hα1 ha hs k
    push_cast
    linarith

theorem psi_quadratic_rate (α : ℕ → ℝ) (hα0 : ∀ k, 0 < α k)
    (hα1 : ∀ k, α k < 1) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ k, a ^ 2 * psi α (k+1) ≤ α k ^ 2) (k : ℕ) :
    psi α k ≤ 1/(1+(k:ℝ)*a/2)^2 := by
  have hp := psi_pos α hα1 k
  have hq := Real.sqrt_pos.mpr hp
  have hd : 0 < 1+(k:ℝ)*a/2 := by positivity
  have h := (le_div_iff₀ hq).mp (psi_inverse_sqrt_lower α hα0 hα1 ha hs k)
  have hb : Real.sqrt (psi α k) ≤ 1/(1+(k:ℝ)*a/2) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hm := mul_le_mul hb hb (Real.sqrt_nonneg (psi α k)) (by positivity)
  simpa only [← pow_two, Real.sq_sqrt hp.le, div_pow, one_pow] using hm

end RandomGradFree.AcceleratedProof

end

/- Complete source body: BiasRecurrence -/
section

set_option autoImplicit false
open RandomGradFree.Accelerated

namespace RandomGradFree.AcceleratedProof

theorem C_eq_forward_sum (α : ℕ → ℝ) (k : ℕ) :
    C α k = ∑ i ∈ Finset.Ico 1 (k+1), ∏ j ∈ Finset.Ico i k, (1-α j) := by
  by_cases hk : k=0
  · simp [hk, C]
  have href := Finset.sum_Ico_reflect
    (fun i => ∏ j ∈ Finset.Ico i k, (1-α j)) 1 (m := k) (n := k) (by omega)
  have href' : (∑ i ∈ Finset.Ico 1 k, ∏ j ∈ Finset.Ico (k-i) k, (1-α j)) =
      ∑ i ∈ Finset.Ico 1 k, ∏ j ∈ Finset.Ico i k, (1-α j) := by
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] using href
  rw [C, if_neg hk, href', Finset.sum_Ico_succ_top (by omega : 1 ≤ k)]
  simp only [Finset.Ico_self, Finset.prod_empty]
  ring

theorem C_succ (α : ℕ → ℝ) (k : ℕ) : C α (k+1) = (1-α k)*C α k+1 := by
  rw [C_eq_forward_sum, Finset.sum_Ico_succ_top (by omega : 1 ≤ k+1)]
  simp only [Finset.Ico_self, Finset.prod_empty]
  rw [C_eq_forward_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have := (Finset.mem_Ico.mp hi).2; omega
  rw [Finset.prod_Ico_succ_top hik]
  ring

theorem C_nonneg (α : ℕ → ℝ) (hα : ∀ k, α k ≤ 1) (k : ℕ) : 0 ≤ C α k := by
  rw [C_eq_forward_sum]
  exact Finset.sum_nonneg fun i _ => Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hα j)

theorem potential_recurrence_bound (α R : ℕ → ℝ) (ξ d : ℝ)
    (hα : ∀ k, α k ≤ 1)
    (hR : ∀ k, R (k+1) ≤ (1-α k)*R k+ξ+α k*d) (k : ℕ) :
    R k ≤ psi α k*R 0+ξ*C α k+d*(1-psi α k) := by
  induction k with
  | zero => simp [psi_zero, C]
  | succ k ih =>
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hα k))
    rw [psi_succ, C_succ]
    nlinarith [hR k]

end RandomGradFree.AcceleratedProof

end

/- Complete source body: AcceleratedMixing -/
section

set_option autoImplicit false

namespace RandomGradFree.AcceleratedProof

theorem mixing_coefficients {g gp a τ : ℝ} (hg : 0 < g) (hgp : 0 < gp)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hτ : 0 ≤ τ)
    (heq : gp = (1-a)*g+a*τ) :
    let l := a/gp*τ
    let b := a*g/(g+a*τ)
    0 ≤ l ∧ l ≤ 1 ∧ gp*(1-l)=(1-a)*g ∧ gp*l=a*τ ∧
      a*(1-l)*(1-b)=(1-a)*b := by
  dsimp
  have hd : 0 < g+a*τ := add_pos_of_pos_of_nonneg hg (mul_nonneg ha0 hτ)
  have hl : gp*(a/gp*τ)=a*τ := by field_simp
  refine ⟨by positivity, ?_, ?_, hl, ?_⟩
  · apply (mul_le_mul_iff_of_pos_left hgp).mp
    rw [hl, mul_one, heq]
    have := mul_nonneg (sub_nonneg.mpr ha1) hg.le
    linarith
  · rw [mul_sub, mul_one, hl, heq]
    ring
  · field_simp
    rw [heq]
    ring

theorem extrapolation_balance {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x v : E) (a l b : ℝ)
    (h : a*(1-l)*(1-b)=(1-a)*b) :
    (a*(1-l)) • ((1-b) • x+b • v-v) =
      (1-a) • (x-((1-b) • x+b • v)) := by
  have hx : (1-b) • x+b • v-v = (1-b) • (x-v) := by module
  have hy : x-((1-b) • x+b • v) = b • (x-v) := by module
  rw [hx, hy, smul_smul, smul_smul, h]

end RandomGradFree.AcceleratedProof
end

/- Complete source body: PotentialGeometry -/
section

set_option autoImplicit false

namespace RandomGradFree.AcceleratedProof

theorem convex_of_tangent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (w : E → E)
    (ht : ∀ x y, F x+inner ℝ (w x) (y-x) ≤ F y) : ConvexOn ℝ Set.univ F := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x+b • y
  have hx := mul_le_mul_of_nonneg_left (ht z x) ha
  have hy := mul_le_mul_of_nonneg_left (ht z y) hb
  have he : a • (x-z)+b • (y-z)=0 := by
    calc
      _ = a • x+b • y-(a+b) • z := by module
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hi := congrArg (fun t : E => inner ℝ (w z) t) he
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hi
  change F z ≤ a*F x+b*F y
  have hw : (a+b)*F z=F z := by rw [hab, one_mul]
  nlinarith

theorem convex_of_strong_tangent {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : E → ℝ) (w : E → E) (τ : ℝ) (hτ : 0 ≤ τ)
    (ht : ∀ x y, F x+inner ℝ (w x) (y-x)+τ/2*‖y-x‖^2 ≤ F y) :
    ConvexOn ℝ Set.univ F := by
  apply convex_of_tangent F w
  intro x y
  have hh := mul_nonneg (show 0 ≤ τ/2 by positivity) (sq_nonneg ‖y-x‖)
  linarith [ht x y]

theorem squared_norm_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    ‖(1-l) • x+l • y‖^2 ≤ (1-l)*‖x‖^2+l*‖y‖^2 := by
  have hc := (convexOn_univ_norm : ConvexOn ℝ Set.univ (fun z : E => ‖z‖)).pow
    (fun z _ => norm_nonneg z) 2
  simpa only [Pi.pow_apply, smul_eq_mul] using hc.2 (Set.mem_univ x) (Set.mem_univ y)
    (sub_nonneg.mpr hl1) hl0 (by ring : (1-l)+l=1)

theorem potential_geometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (x v y z w : E) (g gp a τ l : ℝ)
    (hgp : 0 ≤ gp) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hleft : gp*(1-l)=(1-a)*g) (hright : gp*l=a*τ)
    (hbalance : (a*(1-l)) • (y-v)=(1-a) • (x-y))
    (hz : F y+inner ℝ w (z-y)+τ/2*‖z-y‖^2 ≤ F z)
    (hx : F y+inner ℝ w (x-y) ≤ F x) :
    gp/2*‖(1-l) • v+l • y-z‖^2 +
      a*inner ℝ w (z-((1-l) • v+l • y)) + F y-F z ≤
        (1-a)*(g/2*‖v-z‖^2+F x-F z) := by
  have he : (1-l) • v+l • y-z=(1-l) • (v-z)+l • (y-z) := by module
  have hn := mul_le_mul_of_nonneg_left
    (squared_norm_convex (v-z) (y-z) hl0 hl1) (show 0 ≤ gp/2 by positivity)
  rw [← he] at hn
  have hr : gp/2*((1-l)*‖v-z‖^2+l*‖y-z‖^2) =
      (1-a)*g/2*‖v-z‖^2+a*τ/2*‖z-y‖^2 := by
    calc
      _ = gp*(1-l)/2*‖v-z‖^2+gp*l/2*‖y-z‖^2 := by ring
      _ = _ := by rw [hleft, hright, norm_sub_rev y z]
  rw [hr] at hn
  have hi := congrArg (fun t : E => inner ℝ w t) hbalance
  simp only [inner_smul_right] at hi
  have hm : z-((1-l) • v+l • y)=(z-y)+(1-l) • (y-v) := by module
  have him : a*inner ℝ w (z-((1-l) • v+l • y)) =
      a*inner ℝ w (z-y)+(1-a)*inner ℝ w (x-y) := by
    rw [hm, inner_add_right, inner_smul_right]
    nlinarith [hi]
  rw [him]
  have hz' := mul_le_mul_of_nonneg_left hz ha0
  have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ha1)
  nlinarith

end RandomGradFree.AcceleratedProof

end

/- Complete source body: ExpectationAlgebra -/
section

set_option autoImplicit false
open MeasureTheory

namespace RandomGradFree.AcceleratedProof

variable {D E : Type*} [MeasurableSpace D] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {P : Measure D} [IsProbabilityMeasure P]

theorem norm_affine_square (A : E) (c : ℝ) (r : E) :
    ‖A-c • r‖^2 = ‖A‖^2-2*c*inner ℝ A r+c^2*‖r‖^2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

theorem integrable_norm_affine_square {r : D → E} (hr : Integrable r P)
    (hr2 : Integrable (fun d => ‖r d‖^2) P) (A : E) (c : ℝ) :
    Integrable (fun d => ‖A-c • r d‖^2) P := by
  simp_rw [norm_affine_square]
  exact ((integrable_const _).sub ((hr.const_inner A).const_mul (2*c))).add
    (hr2.const_mul (c^2))

theorem integral_norm_affine_square [CompleteSpace E] {r : D → E} (hr : Integrable r P)
    (hr2 : Integrable (fun d => ‖r d‖^2) P) (A : E) (c : ℝ) :
    (∫ d, ‖A-c • r d‖^2 ∂P) =
      ‖A‖^2-2*c*inner ℝ A (∫ d, r d ∂P)+c^2*(∫ d, ‖r d‖^2 ∂P) := by
  simp_rw [norm_affine_square]
  have hc : Integrable (fun _ : D => ‖A‖^2) P := integrable_const _
  have hsub : Integrable (fun d => ‖A‖^2-2*c*inner ℝ A (r d)) P :=
    hc.sub ((hr.const_inner A).const_mul (2*c))
  rw [integral_add hsub (hr2.const_mul (c^2)),
    integral_sub hc ((hr.const_inner A).const_mul (2*c)),
    integral_const_mul, integral_const_mul, integral_inner hr]
  simp only [integral_const, probReal_univ, one_smul]

theorem smooth_step_integral [CompleteSpace E] {r : D → E} (hr : Integrable r P)
    (hr2 : Integrable (fun d => ‖r d‖^2) P)
    (F : E → ℝ) (y w : E) (h L lower : ℝ)
    (hm : AEStronglyMeasurable (fun d => F (y-h • r d)) P)
    (hlower : ∀ d, lower ≤ F (y-h • r d))
    (hupper : ∀ d, F (y-h • r d) ≤
      F y-h*inner ℝ w (r d)+h^2*L/2*‖r d‖^2)
    (hmean : (∫ d, r d ∂P)=w) :
    Integrable (fun d => F (y-h • r d)) P ∧
      (∫ d, F (y-h • r d) ∂P) ≤ F y-h*‖w‖^2+h^2*L/2*(∫ d, ‖r d‖^2 ∂P) := by
  have hu : Integrable (fun d => F y-h*inner ℝ w (r d)+h^2*L/2*‖r d‖^2) P :=
    ((integrable_const _).sub ((hr.const_inner w).const_mul h)).add
      (hr2.const_mul (h^2*L/2))
  have hi := integrable_of_le_of_le hm (ae_of_all _ hlower) (ae_of_all _ hupper)
    (integrable_const lower) hu
  refine ⟨hi, ?_⟩
  have hh := integral_mono_ae hi hu (ae_of_all _ hupper)
  have hc : Integrable (fun _ : D => F y) P := integrable_const _
  have hsub : Integrable (fun d => F y-h*inner ℝ w (r d)) P :=
    hc.sub ((hr.const_inner w).const_mul h)
  rw [integral_add hsub (hr2.const_mul (h^2*L/2)),
    integral_sub hc ((hr.const_inner w).const_mul h),
    integral_const_mul, integral_const_mul, integral_inner hr, hmean] at hh
  simpa only [integral_const, probReal_univ, one_smul, real_inner_self_eq_norm_sq] using hh

end RandomGradFree.AcceleratedProof

end

/- Complete source body: VarianceCancellation -/
section

set_option autoImplicit false
open MeasureTheory

namespace RandomGradFree.AcceleratedProof

theorem variance_cancellation {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Measure D) [IsProbabilityMeasure P]
    (r : D → E) (hr : Integrable r P)
    (hr2 : Integrable (fun d => ‖r d‖^2) P)
    (F : E → ℝ) (y mid z w : E) (gp θ a h ξ base : ℝ)
    (ha : 0 < a) (hs : a^2=θ*gp)
    (hmean : (∫ d, r d ∂P)=w)
    (hFi : Integrable (fun d => F (y-h • r d)) P)
    (hF : (∫ d, F (y-h • r d) ∂P) ≤
      F y-θ/2*(∫ d, ‖r d‖^2 ∂P)+ξ) :
    Integrable (fun d => gp/2*‖mid-(θ/a) • r d-z‖^2+F (y-h • r d)-base) P ∧
    (∫ d, gp/2*‖mid-(θ/a) • r d-z‖^2+F (y-h • r d)-base ∂P) ≤
      gp/2*‖mid-z‖^2+a*inner ℝ w (z-mid)+F y-base+ξ := by
  have he (d : D) : mid-(θ/a) • r d-z=(mid-z)-(θ/a) • r d := by abel
  have hni : Integrable (fun d => ‖mid-(θ/a) • r d-z‖^2) P := by
    simp_rw [he]
    exact integrable_norm_affine_square hr hr2 (mid-z) (θ/a)
  have hsum : Integrable (fun d => gp/2*‖mid-(θ/a) • r d-z‖^2+F (y-h • r d)) P :=
    (hni.const_mul (gp/2)).add hFi
  refine ⟨hsum.sub (integrable_const base), ?_⟩
  rw [integral_sub hsum (integrable_const base),
    integral_add (hni.const_mul (gp/2)) hFi, integral_const_mul]
  have hn : (∫ d, ‖mid-(θ/a) • r d-z‖^2 ∂P) =
      ‖mid-z‖^2-2*(θ/a)*inner ℝ (mid-z) w+(θ/a)^2*(∫ d, ‖r d‖^2 ∂P) := by
    simp_rw [he]
    rw [integral_norm_affine_square hr hr2, hmean]
  rw [hn]
  simp only [integral_const, probReal_univ, one_smul]
  have hc : gp*(θ/a)=a := by
    rw [← mul_div_assoc]
    apply (div_eq_iff ha.ne').mpr
    nlinarith [hs]
  have hc2 : gp*(θ/a)^2=θ := by
    calc
      _ = (gp*(θ/a))*(θ/a) := by ring
      _ = θ := by rw [hc]; field_simp
  have hi : inner ℝ w (z-mid) = -inner ℝ (mid-z) w := by
    rw [← neg_sub mid z, inner_neg_right, real_inner_comm]
  rw [hi]
  have hexp : gp/2*(‖mid-z‖^2-2*(θ/a)*inner ℝ (mid-z) w+
      (θ/a)^2*(∫ d, ‖r d‖^2 ∂P)) =
      gp/2*‖mid-z‖^2-a*inner ℝ (mid-z) w+θ/2*(∫ d, ‖r d‖^2 ∂P) := by
    calc
      _ = gp/2*‖mid-z‖^2-(gp*(θ/a))*inner ℝ (mid-z) w+
          (gp*(θ/a)^2)/2*(∫ d, ‖r d‖^2 ∂P) := by ring
      _ = _ := by rw [hc, hc2]
  rw [hexp]
  linarith

theorem potential_integral_step {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Measure D) [IsProbabilityMeasure P]
    (r : D → E) (hr : Integrable r P)
    (hr2 : Integrable (fun d => ‖r d‖^2) P)
    (F : E → ℝ) (x v y z w : E) (g gp a τ l θ h ξ base : ℝ)
    (hgp : 0 ≤ gp) (ha : 0 < a) (ha1 : a ≤ 1)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hs : a^2=θ*gp)
    (hleft : gp*(1-l)=(1-a)*g) (hright : gp*l=a*τ)
    (hbalance : (a*(1-l)) • (y-v)=(1-a) • (x-y))
    (hz : F y+inner ℝ w (z-y)+τ/2*‖z-y‖^2 ≤ F z)
    (hx : F y+inner ℝ w (x-y) ≤ F x)
    (hmean : (∫ d, r d ∂P)=w)
    (hFi : Integrable (fun d => F (y-h • r d)) P)
    (hF : (∫ d, F (y-h • r d) ∂P) ≤
      F y-θ/2*(∫ d, ‖r d‖^2 ∂P)+ξ) :
    Integrable (fun d => gp/2*‖(1-l) • v+l • y-(θ/a) • r d-z‖^2+
      F (y-h • r d)-base) P ∧
    (∫ d, gp/2*‖(1-l) • v+l • y-(θ/a) • r d-z‖^2+
      F (y-h • r d)-base ∂P) ≤
      (1-a)*(g/2*‖v-z‖^2+F x-base)+ξ+a*(F z-base) := by
  have hi := variance_cancellation P r hr hr2 F y ((1-l) • v+l • y) z w
    gp θ a h ξ base ha hs hmean hFi hF
  refine ⟨hi.1, ?_⟩
  have hg := potential_geometry F x v y z w g gp a τ l hgp ha.le ha1 hl0 hl1
    hleft hright hbalance hz hx
  linarith [hi.2]

end RandomGradFree.AcceleratedProof

end

/- Complete source body: PotentialModel -/
section

set_option autoImplicit false

namespace RandomGradFree.AcceleratedProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def statePotential (F : E → ℝ) (z : E) (base g : ℝ) (s : E × E) : ℝ :=
  g/2*‖s.2-z‖^2+F s.1-base

noncomputable def trialPoint (τ g a : ℝ) (s : E × E) : E :=
  (1-a*g/(g+a*τ)) • s.1+(a*g/(g+a*τ)) • s.2

noncomputable def nextState (f : E → ℝ) (μ τ g gp a θ h : ℝ)
    (s : E × E) (d : E) : E × E :=
  let y := trialPoint τ g a s
  let r := Shared.oracle f μ y d
  (y-h • r, (1-a/gp*τ) • s.2+(a/gp*τ) • y-(θ/a) • r)

omit [InnerProductSpace ℝ E] in
theorem statePotential_nonneg (F : E → ℝ) (z : E) (base g : ℝ)
    (hg : 0 ≤ g) (hF : ∀ x, base ≤ F x) (s : E × E) :
    0 ≤ statePotential F z base g s := by
  unfold statePotential
  have hh := mul_nonneg (show 0 ≤ g/2 by positivity) (sq_nonneg ‖s.2-z‖)
  linarith [hF s.1]

omit [InnerProductSpace ℝ E] in
theorem statePotential_continuous (F : E → ℝ) (hF : Continuous F)
    (z : E) (base g : ℝ) : Continuous (statePotential F z base g) := by
  unfold statePotential
  fun_prop

theorem nextState_continuous (f : E → ℝ) (μ τ g gp a θ h : ℝ)
    (ho : Continuous (fun p : E × E => Shared.oracle f μ p.1 p.2)) :
    Continuous (fun p : (E × E) × E => nextState f μ τ g gp a θ h p.1 p.2) := by
  have hy : Continuous (fun p : (E × E) × E => trialPoint τ g a p.1) := by
    unfold trialPoint
    fun_prop
  have hr := ho.comp (hy.prodMk continuous_snd)
  exact (hy.sub (continuous_const.smul hr)).prodMk
    (((continuous_const.smul continuous_fst.snd).add (continuous_const.smul hy)).sub
      (continuous_const.smul hr))

end RandomGradFree.AcceleratedProof
end

end

/- Complete checked assembly: AnalyticTransport -/
section

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace RandomGradFree.AcceleratedProof
open RandomGradFree.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem smoothing_zero (f : E → ℝ) : smoothing f 0 = f := by
  funext x
  simp [smoothing]

theorem oracle_zero (f : E → ℝ) (hd : Differentiable ℝ f) (x u : E) :
    oracle f 0 x u = fderiv ℝ f x u • u := by
  rw [RG33.oracle_eq hd]
  simp [RG33.coef, inner_gradient_left]

theorem oracle_continuous (f : E → ℝ) (L μ : ℝ) (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖) :
    Continuous (fun p : E × E => oracle f μ p.1 p.2) := by
  have he : (fun p : E × E => oracle f μ p.1 p.2) =
      (fun p : E × E => RG33.coef f μ p.1 p.2 • p.2) :=
    funext fun p => RG33.oracle_eq hd p.1 p.2
  rw [he]
  exact (RG33.coef_cont_joint hd hg).smul continuous_snd

theorem oracle_sq_integrable (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (fun u => ‖oracle f μ x u‖^2) (stdGaussian E) := by
  by_cases hz : μ = 0
  · subst μ
    simp_rw [oracle_zero f hd]
    exact AcceleratedSource.OracleMoment.RandomProof.directional_integrable (fderiv ℝ f x)
  · have hp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hz)
    have h6 : Integrable (fun u : E => ‖u‖^6) (stdGaussian E) :=
      (IsGaussian.memLp_id (stdGaussian E) (6:ℕ) (by simp)).integrable_norm_pow (by norm_num)
    have hdint := AcceleratedSource.OracleMoment.RandomProof.directional_integrable (fderiv ℝ f x)
    refine Integrable.mono' ((h6.const_mul (μ^2/2*L^2)).add (hdint.const_mul 2))
      (((oracle_continuous f L μ hd hg).comp (continuous_const.prodMk continuous_id)).norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact AcceleratedSource.OracleMoment.RandomProof.oracle_point f L hL hd hg μ hp x u

theorem oracle_integrable (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (oracle f μ x) (stdGaussian E) := by
  have hm : AEStronglyMeasurable (oracle f μ x) (stdGaussian E) :=
    ((oracle_continuous f L μ hd hg).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    ((memLp_two_iff_integrable_sq_norm hm).2 (oracle_sq_integrable f L hL hd hg μ hμ x))

theorem smoothing_regular (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    Differentiable ℝ (smoothing f μ) ∧
      ∀ x y, ‖gradient (smoothing f μ) x-gradient (smoothing f μ) y‖ ≤ L*‖x-y‖ :=
  AcceleratedSource.GradientLipschitz.accepted f L hL hd hg μ hμ

theorem oracle_mean (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    ∫ u, oracle f μ x u ∂stdGaussian E = gradient (smoothing f μ) x := by
  by_cases hz : μ = 0
  · subst μ
    rw [smoothing_zero]
    simp_rw [oracle_zero f hd]
    exact AcceleratedSource.DirectionalMean.accepted f x (hd x)
  · exact (AcceleratedSource.SmoothingGradient.RandomGradFree.Accelerated.accepted
      f L hL hd hg μ (lt_of_le_of_ne hμ (Ne.symm hz)) x).gradient.symm

theorem oracle_second_moment (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    ∫ u, ‖oracle f μ x u‖^2 ∂stdGaussian E ≤
      4 * ((Module.finrank ℝ E : ℝ)+4) * ‖gradient (smoothing f μ) x‖^2 +
      3*μ^2*L^2*((Module.finrank ℝ E : ℝ)+4)^3 := by
  by_cases hz : μ = 0
  · subst μ
    rw [smoothing_zero]
    simp_rw [oracle_zero f hd]
    have hh := AcceleratedSource.OracleMoment.RandomProof.directional_bound f x (hd x)
    have hn : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg ‖gradient f x‖]
  · exact AcceleratedSource.OracleMoment.RandomGradFree.Accelerated.accepted
      f L hL hd hg μ (lt_of_le_of_ne hμ (Ne.symm hz)) x

theorem smoothing_integrable (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (fun u => f (x+μ • u)) (stdGaussian E) :=
  (AcceleratedSource.SmoothingGradient.RandomStein.smooth_integrable f L hL hd hg μ hμ x).1

theorem smoothing_bounds (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L : ℝ) (hL : 0 ≤ L) (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    f x ≤ smoothing f μ x ∧ smoothing f μ x - f x ≤ μ^2/2*L*Module.finrank ℝ E := by
  refine ⟨AcceleratedSource.SmoothingJensen.accepted f hf μ hμ x
    (smoothing_integrable f L hL hd hg μ hμ x), ?_⟩
  exact (le_abs_self _).trans (AcceleratedSource.SmoothingApprox.accepted f L hL hd hg μ hμ x)

end RandomGradFree.AcceleratedProof

end

section

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.AcceleratedProof
open RandomGradFree.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian smoothing preserves the original strong-convexity parameter. -/
theorem smoothing_strong_tangent (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : Differentiable ℝ f)
    (hg : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (τ : ℝ)
    (hsc : ∀ x y, f x + inner ℝ (gradient f x) (y-x) + τ/2*‖y-x‖^2 ≤ f y)
    (μ : ℝ) (hμ : 0 ≤ μ) (x y : E) :
    smoothing f μ x + inner ℝ (gradient (smoothing f μ) x) (y-x) +
      τ/2*‖y-x‖^2 ≤ smoothing f μ y := by
  have hfd : ∀ a b, ‖fderiv ℝ f a-fderiv ℝ f b‖ ≤ L*‖a-b‖ := by
    intro a b
    rw [AcceleratedSource.GradientLipschitz.RandomGradFree.Accelerated.aux_sgl_fderiv_eq f a,
      AcceleratedSource.GradientLipschitz.RandomGradFree.Accelerated.aux_sgl_fderiv_eq f b,
      ← map_sub, LinearIsometryEquiv.norm_map]
    exact hg a b
  have hmain := AcceleratedSource.GradientLipschitz.RandomGradFree.Accelerated.aux_sgl_main
    f L hL hd hfd μ hμ x
  have hi : Integrable (fun u => fderiv ℝ f (x+μ • u) (y-x)) (stdGaussian E) :=
    (ContinuousLinearMap.apply ℝ ℝ (y-x)).integrable_comp hmain.1
  have hix := smoothing_integrable f L hL hd hg μ hμ x
  have hiy := smoothing_integrable f L hL hd hg μ hμ y
  have hpoint (u : E) : f (x+μ • u) + fderiv ℝ f (x+μ • u) (y-x) +
      τ/2*‖y-x‖^2 ≤ f (y+μ • u) := by
    have hh := hsc (x+μ • u) (y+μ • u)
    have he : (y+μ • u)-(x+μ • u) = y-x := by abel
    rw [he, inner_gradient_left] at hh
    exact hh
  have hint := integral_mono ((hix.add hi).add (integrable_const (τ/2*‖y-x‖^2)))
    hiy hpoint
  simp only [Pi.add_apply] at hint
  have hsplit : (∫ u, f (x+μ • u) + fderiv ℝ f (x+μ • u) (y-x) +
      τ/2*‖y-x‖^2 ∂stdGaussian E) =
      (∫ u, f (x+μ • u) ∂stdGaussian E) +
      (∫ u, fderiv ℝ f (x+μ • u) (y-x) ∂stdGaussian E) + τ/2*‖y-x‖^2 := by
    have hh := integral_add (hix.add hi) (integrable_const (τ/2*‖y-x‖^2))
    simp only [Pi.add_apply] at hh
    rw [integral_add hix hi, integral_const, probReal_univ, one_smul] at hh
    exact hh
  rw [hsplit, ← ContinuousLinearMap.integral_apply hmain.1 (y-x)] at hint
  have he : (∫ u, fderiv ℝ f (x+μ • u) ∂stdGaussian E) (y-x) =
      inner ℝ (gradient (smoothing f μ) x) (y-x) := by
    rw [inner_gradient_left, hmain.2.fderiv]
  rw [he] at hint
  exact hint

end RandomGradFree.AcceleratedProof

end

section

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.AcceleratedProof
open RandomGradFree.Accelerated

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {f : E → ℝ} {μ τ θ h : ℝ} {x₀ : E} {γ α : ℕ → ℝ}
  {u x v : ℕ → Ω → E}

/-- Two-state adaptation of Nickrobbins95's history/product-law proof,
accepted submission 9bae62cb-8ff0-44e7-aa81-07d2d1096a03. -/
theorem run_state_transport
    (horacle : Continuous (fun p : E × E => Shared.oracle f μ p.1 p.2))
    (hrun : IsAcceleratedRandomRun P f μ τ θ h x₀ γ α u x v) :
    ∀ k, Measurable (fun ω => (x k ω, v k ω)) ∧
      IndepFun (fun ω => (x k ω, v k ω)) (u k) P ∧
      ∀ G : (E × E) × E → ENNReal, Measurable G →
        ∫⁻ ω, G ((x k ω, v k ω), u k ω) ∂P =
          ∫⁻ ω, (∫⁻ d, G ((x k ω, v k ω), d) ∂stdGaussian E) ∂P := by
  let state : ℕ → Ω → E × E := fun k ω => (x k ω, v k ω)
  let history : ℕ → MeasurableSpace Ω := fun k =>
    ⨆ j ∈ Set.Iio k, (inferInstance : MeasurableSpace E).comap (u j)
  have hu := hrun.measurable_dir
  have hle : ∀ k, history k ≤ ‹MeasurableSpace Ω› :=
    fun k => iSup₂_le fun j _ => (hu j).comap_le
  let update : ℕ → (E × E) × E → E × E := fun k p =>
    let y := extrap τ γ α k p.1.1 p.1.2
    let g := Shared.oracle f μ y p.2
    (y - h • g, (1 - lam τ γ α k) • p.1.2 + lam τ γ α k • y - (θ / α k) • g)
  have hc : ∀ k, Continuous (update k) := by
    intro k
    have hy : Continuous (fun p : (E × E) × E => extrap τ γ α k p.1.1 p.1.2) := by
      unfold extrap
      fun_prop
    have hg := horacle.comp (hy.prodMk continuous_snd)
    exact (hy.sub (continuous_const.smul hg)).prodMk
      (((continuous_const.smul continuous_fst.snd).add (continuous_const.smul hy)).sub
        (continuous_const.smul hg))
  have hs : ∀ k, state (k+1) = fun ω => update k (state k ω, u k ω) := by
    intro k
    funext ω
    apply Prod.ext
    · exact hrun.step_x k ω
    · exact hrun.step_v k ω
  have hm : ∀ k, Measurable[history k] (state k) := by
    intro k
    induction k with
    | zero =>
      have he : state 0 = fun _ => (x₀, x₀) := by
        funext ω
        simp [state, hrun.init_x, hrun.init_v]
      rw [he]
      exact measurable_const
    | succ k ih =>
      rw [hs k]
      have hmono : history k ≤ history (k+1) := iSup₂_le fun j hj =>
        le_iSup₂_of_le (f := fun j (_ : j ∈ Set.Iio (k+1)) =>
          (inferInstance : MeasurableSpace E).comap (u j)) j
          (show j ∈ Set.Iio (k+1) from lt_trans hj (Nat.lt_succ_self k)) le_rfl
      have huk : Measurable[history (k+1)] (u k) := Measurable.of_comap_le
        (le_iSup₂_of_le (f := fun j (_ : j ∈ Set.Iio (k+1)) =>
          (inferInstance : MeasurableSpace E).comap (u j)) k (Nat.lt_succ_self k) le_rfl)
      exact (hc k).measurable.comp ((ih.mono hmono le_rfl).prodMk huk)
  have hstate : ∀ k, Measurable (state k) := fun k => (hm k).mono (hle k) le_rfl
  have hind : ∀ k, IndepFun (state k) (u k) P := by
    intro k
    have hI := indep_iSup_of_disjoint
      (m := fun j => (inferInstance : MeasurableSpace E).comap (u j))
      (fun j => (hu j).comap_le) hrun.indep_dir.iIndep (S := Set.Iio k) (T := {k})
      (Set.disjoint_singleton_right.mpr (lt_irrefl k))
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hI (hm k).comap_le)
      (le_iSup₂_of_le (f := fun j (_ : j ∈ ({k} : Set ℕ)) =>
        (inferInstance : MeasurableSpace E).comap (u j)) k (Set.mem_singleton k) le_rfl)
  intro k
  refine ⟨hstate k, hind k, ?_⟩
  intro G hG
  have hmap : P.map (fun ω => (state k ω, u k ω)) =
      (P.map (state k)).prod (stdGaussian E) := by
    rw [← hrun.law_dir k]
    exact (indepFun_iff_map_prod_eq_prod_map_map (hstate k).aemeasurable
      (hu k).aemeasurable).mp (hind k)
  change ∫⁻ ω, G (state k ω, u k ω) ∂P =
    ∫⁻ ω, (∫⁻ d, G (state k ω, d) ∂stdGaussian E) ∂P
  rw [← lintegral_map hG ((hstate k).prodMk (hu k)), hmap,
    lintegral_prod _ hG.aemeasurable, lintegral_map hG.lintegral_prod_right' (hstate k)]

end RandomGradFree.AcceleratedProof

end

section

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.AcceleratedProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {f : E → ℝ} {μ τ θ h : ℝ} {x₀ : E} {γ α : ℕ → ℝ}
  {u x v : ℕ → Ω → E}

/-- Tonelli proves finiteness before conversion to real expectations. -/
theorem run_nonnegative_potential
    (horacle : Continuous (fun p : E × E => Shared.oracle f μ p.1 p.2))
    (hrun : Accelerated.IsAcceleratedRandomRun P f μ τ θ h x₀ γ α u x v)
    (Q : ℕ → E × E → ℝ) (hQm : ∀ k, Measurable (Q k))
    (hQ0 : ∀ k s, 0 ≤ Q k s)
    (K : ℕ → (E × E) × E → ℝ) (hKm : ∀ k, Measurable (K k))
    (hK0 : ∀ k s d, 0 ≤ K k (s,d))
    (hKi : ∀ k s, Integrable (fun d => K k (s,d)) (stdGaussian E))
    (hstep : ∀ k ω, Q (k+1) (x (k+1) ω,v (k+1) ω) = K k ((x k ω,v k ω),u k ω))
    (a b : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hbound : ∀ k s, (∫ d, K k (s,d) ∂stdGaussian E) ≤ a k * Q k s + b k) :
    (∀ k, Integrable (fun ω => Q k (x k ω,v k ω)) P) ∧
    (∀ k, (∫ ω, Q (k+1) (x (k+1) ω,v (k+1) ω) ∂P) ≤
      a k * (∫ ω, Q k (x k ω,v k ω) ∂P) + b k) := by
  have htrans := run_state_transport horacle hrun
  let r : ℕ → ENNReal := fun k => ∫⁻ ω, ENNReal.ofReal (Q k (x k ω,v k ω)) ∂P
  have hmeas : ∀ k, Measurable (fun ω => ENNReal.ofReal (Q k (x k ω,v k ω))) :=
    fun k => ((hQm k).comp (htrans k).1).ennreal_ofReal
  have hrec : ∀ k, r (k+1) ≤ ENNReal.ofReal (a k) * r k + ENNReal.ofReal (b k) := by
    intro k
    have hGm : Measurable (fun p => ENNReal.ofReal (K k p)) := (hKm k).ennreal_ofReal
    have he : r (k+1) = ∫⁻ ω, (∫⁻ d, ENNReal.ofReal (K k ((x k ω,v k ω),d))
        ∂stdGaussian E) ∂P := by
      dsimp only [r]
      simp_rw [hstep k]
      exact (htrans k).2.2 _ hGm
    rw [he]
    calc
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (a k) * ENNReal.ofReal (Q k (x k ω,v k ω)) +
          ENNReal.ofReal (b k)) ∂P := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [← ofReal_integral_eq_lintegral_ofReal (hKi k (x k ω,v k ω))
          (ae_of_all _ (hK0 k (x k ω,v k ω)))]
        exact (ENNReal.ofReal_le_ofReal (hbound k (x k ω,v k ω))).trans (by
          rw [ENNReal.ofReal_add (mul_nonneg (ha k) (hQ0 k _)) (hb k),
            ENNReal.ofReal_mul (ha k)])
      _ = _ := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul _ (hmeas k), lintegral_const, measure_univ, mul_one]
  have hr0 : r 0 = ENNReal.ofReal (Q 0 (x₀,x₀)) := by
    simp [r, hrun.init_x, hrun.init_v]
  have hfin : ∀ k, r k ≠ ⊤ := by
    intro k
    induction k with
    | zero => rw [hr0]; exact ENNReal.ofReal_ne_top
    | succ k ih =>
      exact ne_top_of_le_ne_top
        (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ih, ENNReal.ofReal_ne_top⟩)
        (hrec k)
  have hint : ∀ k, Integrable (fun ω => Q k (x k ω,v k ω)) P := by
    intro k
    refine ⟨((hQm k).comp (htrans k).1).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => hQ0 k _)).mpr
      (lt_top_iff_ne_top.mpr (hfin k))
  refine ⟨hint, ?_⟩
  intro k
  have he (j : ℕ) : ∫ ω, Q j (x j ω,v j ω) ∂P = (r j).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => hQ0 j _)
      ((hQm j).comp (htrans j).1).aestronglyMeasurable
  rw [he (k+1), he k]
  have hh := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin k), ENNReal.ofReal_ne_top⟩)
    (hrec k)
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin k)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (ha k), ENNReal.toReal_ofReal (hb k)] at hh

/-- The nonnegative objective gap is dominated by the finite potential. -/
theorem objective_integrable_of_potential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F Q : Ω → ℝ) (c : ℝ) (hFm : AEStronglyMeasurable F P)
    (hQi : Integrable Q P) (hlower : ∀ ω, c ≤ F ω)
    (hupper : ∀ ω, F ω-c ≤ Q ω) :
    Integrable F P ∧ (∫ ω, F ω ∂P)-c ≤ ∫ ω, Q ω ∂P := by
  have hu : ∀ ω, F ω ≤ Q ω+c := fun ω => by linarith [hupper ω]
  have hi := integrable_of_le_of_le hFm (ae_of_all _ hlower) (ae_of_all _ hu)
    (integrable_const c) (hQi.add (integrable_const c))
  refine ⟨hi, ?_⟩
  have hh := integral_mono (hi.sub (integrable_const c)) hQi hupper
  simp only [Pi.sub_apply] at hh
  simpa only [integral_sub hi (integrable_const c), integral_const, probReal_univ, one_smul] using hh

end RandomGradFree.AcceleratedProof

end

end

/- Complete checked assembly: FinalDevelopment -/
section

set_option autoImplicit false

/- Complete source body: ScalarRates -/
section

set_option autoImplicit false
open RandomGradFree.Accelerated

namespace RandomGradFree.AcceleratedProof

theorem scaled_sqrt_square {n L t : ℝ} (hn : 0 ≤ n) (hL : 0 < L) (ht : 0 ≤ t) :
    (Real.sqrt (t/L)/(4*(n+4)))^2 = (1/(16*(n+4)^2*L))*t := by
  have hn4 : n+4 ≠ 0 := by linarith
  rw [div_pow, Real.sq_sqrt (div_nonneg ht hL.le)]
  field_simp
  ring

theorem coefficient_rate_bounds (n : ℕ) (L τ θ : ℝ) (hL : 0 < L)
    (hτ : 0 ≤ τ) (hτL : τ ≤ L) (hθ : θ=1/(16*((n:ℝ)+4)^2*L))
    (γ α : ℕ → ℝ) (hγ0 : 0 < γ 0) (hτγ0 : τ ≤ γ 0)
    (hα : ∀ k, 0 < α k)
    (heq : ∀ k, α k^2/θ=(1-α k)*γ k+α k*τ)
    (hγ : ∀ k, γ (k+1)=(1-α k)*γ k+α k*τ) (k : ℕ) :
    psi α k ≤ (1-Real.sqrt (τ/L)/(4*((n:ℝ)+4)))^k ∧
    psi α k ≤ 1/(1+(k:ℝ)/(8*((n:ℝ)+4))*Real.sqrt (γ 0/L))^2 ∧
    C α k ≤ (k:ℝ) ∧
    (0<τ → C α k ≤ 4*((n:ℝ)+4)/Real.sqrt (τ/L)) := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hθp : 0<θ := by rw [hθ]; exact (theta_pos_and_small hn hL hτL).1
  have hθτ : θ*τ<1 := by rw [hθ]; exact (theta_pos_and_small hn hL hτL).2
  have hgb := coefficient_gamma_bounds hτ hθp hθτ γ α hγ0 hτγ0 hα heq hγ
  have ha1 := coefficient_alpha_lt_one hτ hθp hθτ γ α hγ0 hτγ0 hα heq hγ
  have har (j : ℕ) : 0≤α j ∧ α j≤1 := ⟨(hα j).le, (ha1 j).le⟩
  have hs (j : ℕ) : α j^2=θ*γ (j+1) := by
    apply coefficient_square hθp.ne' γ α _ j
    intro i
    rw [heq i, hγ i]
  have ht (j : ℕ) : Real.sqrt (τ/L)/(4*((n:ℝ)+4)) ≤ α j := by
    have hsq := scaled_sqrt_square hn hL hτ
    rw [← hθ] at hsq
    have hm := mul_le_mul_of_nonneg_left (hgb (j+1)).2.1 hθp.le
    have hp : 0 ≤ Real.sqrt (τ/L)/(4*((n:ℝ)+4)) := by positivity
    nlinarith [hs j, hα j]
  refine ⟨AcceleratedSource.PsiLinear.accepted α n (τ/L) har
    (div_nonneg hτ hL.le) ((div_le_one₀ hL).mpr hτL) ht k, ?_,
    AcceleratedSource.CLinear.accepted α har k,
    fun htau => AcceleratedSource.CStrong.accepted n α har τ htau L hL ht k⟩
  let a := Real.sqrt (γ 0/L)/(4*((n:ℝ)+4))
  have ha : 0≤a := by dsimp [a]; positivity
  have he : a^2=θ*γ 0 := by
    dsimp [a]
    rw [hθ]
    exact scaled_sqrt_square hn hL hγ0.le
  have hkey (j : ℕ) : a^2*psi α (j+1) ≤ α j^2 := by
    rw [he]
    exact alpha_square_ge_psi τ θ hτ hθp.le γ α
      (fun i => (har i).1) (fun i => (har i).2) hγ hs j
  have hp := psi_quadratic_rate α hα ha1 ha hkey k
  have heqden : 1+(k:ℝ)*a/2=1+(k:ℝ)/(8*((n:ℝ)+4))*Real.sqrt (γ 0/L) := by
    dsimp [a]
    have hn4 : (n:ℝ)+4 ≠ 0 := by positivity
    field_simp
    ring
  rwa [heqden] at hp

end RandomGradFree.AcceleratedProof

end

/- Complete source body: OracleDescent -/
section

set_option autoImplicit false
open MeasureTheory

namespace RandomGradFree.AcceleratedProof

theorem oracle_descent {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : Measure D) [IsProbabilityMeasure P]
    (F : E → ℝ) (L : ℝ) (hL : 0<L) (hd : Differentiable ℝ F)
    (hgrad : ∀ x y, ‖gradient F x-gradient F y‖ ≤ L*‖x-y‖)
    (y : E) (r : D → E) (hr : Integrable r P)
    (hr2 : Integrable (fun d => ‖r d‖^2) P)
    (hmean : (∫ d, r d ∂P)=gradient F y)
    (n μ θ h base : ℝ) (hn : 2≤n)
    (hθ : θ=1/(16*(n+4)^2*L)) (hh : h=1/(4*(n+4)*L))
    (hm : AEStronglyMeasurable (fun d => F (y-h • r d)) P)
    (hlow : ∀ d, base ≤ F (y-h • r d))
    (hmoment : (∫ d, ‖r d‖^2 ∂P) ≤ 4*(n+4)*‖gradient F y‖^2+3*μ^2*L^2*(n+4)^3) :
    Integrable (fun d => F (y-h • r d)) P ∧
    (∫ d, F (y-h • r d) ∂P) ≤ F y-θ/2*(∫ d, ‖r d‖^2 ∂P)+3*μ^2*L*(n+8)/16 := by
  have hu (d : D) : F (y-h • r d) ≤
      F y-h*inner ℝ (gradient F y) (r d)+h^2*L/2*‖r d‖^2 := by
    have hdesc := AcceleratedSource.OracleMoment.RandomGradFree.Smooth.aux_sa_descent
      F L hd hgrad y (-(h • r d))
    have hup := (le_abs_self _).trans hdesc
    simp only [← sub_eq_add_neg, inner_neg_right, inner_smul_right, norm_neg,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hup
    linarith only [hup]
  have hs := smooth_step_integral hr hr2 F y (gradient F y) h L base hm hlow hu hmean
  exact ⟨hs.1, moment_to_descent hn hL hθ hh hmoment hs.2⟩

end RandomGradFree.AcceleratedProof

end

/- Complete source body: FixedStatePotential -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace RandomGradFree.AcceleratedProof
open RandomGradFree.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fixed_state_potential (hdim : 2 ≤ Module.finrank ℝ E)
    (f : E → ℝ) (L : ℝ) (hL : 0 < L) (hd : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hsc : ∀ x y, f x+inner ℝ (gradient f x) (y-x)+τ/2*‖y-x‖^2 ≤ f y)
    (z : E) (hopt : ∀ x, f z ≤ f x) (μ : ℝ) (hμ : 0 ≤ μ)
    (θ h : ℝ) (hθ : θ=1/(16*((Module.finrank ℝ E:ℝ)+4)^2*L))
    (hh : h=1/(4*((Module.finrank ℝ E:ℝ)+4)*L))
    (g gp a : ℝ) (hg : 0<g) (hgp : 0<gp) (ha : 0<a) (ha1 : a≤1)
    (hrec : gp=(1-a)*g+a*τ) (hs : a^2=θ*gp) (s : E × E) :
    Integrable (fun d => statePotential (smoothing f μ) z (f z) gp
      (nextState f μ τ g gp a θ h s d)) (stdGaussian E) ∧
    (∫ d, statePotential (smoothing f μ) z (f z) gp
      (nextState f μ τ g gp a θ h s d) ∂stdGaussian E) ≤
      (1-a)*statePotential (smoothing f μ) z (f z) g s+
      3*μ^2*L*((Module.finrank ℝ E:ℝ)+8)/16+a*(smoothing f μ z-f z) := by
  let F := smoothing f μ
  let y := trialPoint τ g a s
  let r := oracle f μ y
  let w := gradient F y
  let l := a/gp*τ
  have hreg := smoothing_regular f L hL.le hd hgrad μ hμ
  have hfconv := convex_of_strong_tangent f (gradient f) τ hτ hsc
  have hlow (x : E) : f z ≤ F x :=
    (hopt x).trans (smoothing_bounds f hfconv L hL.le hd hgrad μ hμ x).1
  have hr := oracle_integrable f L hL.le hd hgrad μ hμ y
  have hr2 := oracle_sq_integrable f L hL.le hd hgrad μ hμ y
  have hmean : (∫ d, r d ∂stdGaussian E)=w := oracle_mean f L hL.le hd hgrad μ hμ y
  have hpair : Continuous (fun d : E => (y,d)) := continuous_const.prodMk continuous_id
  have hrcont := (oracle_continuous f L μ hd hgrad).comp hpair
  change Continuous r at hrcont
  have hFc : Continuous F := hreg.1.continuous
  have hyc : Continuous (fun _ : E => y) := continuous_const
  have hhc : Continuous (fun _ : E => h) := continuous_const
  have hstepcont := hyc.sub (hhc.smul hrcont)
  change Continuous (fun d : E => y-h • r d) at hstepcont
  have hFstep := hFc.comp hstepcont
  have hm : AEStronglyMeasurable (fun d => F (y-h • r d)) (stdGaussian E) :=
    hFstep.aestronglyMeasurable
  have hdstep := oracle_descent (stdGaussian E) F L hL hreg.1 hreg.2 y r hr hr2 hmean
    (Module.finrank ℝ E:ℝ) μ θ h (f z) (by exact_mod_cast hdim) hθ hh hm
    (fun d => hlow _) (oracle_second_moment f L hL.le hd hgrad μ hμ y)
  obtain ⟨hl0, hl1, hleft, hright, hbal⟩ := mixing_coefficients hg hgp ha.le ha1 hτ hrec
  have hbalance : (a*(1-l)) • (y-s.2)=(1-a) • (s.1-y) :=
    extrapolation_balance s.1 s.2 a l (a*g/(g+a*τ)) hbal
  have hz := smoothing_strong_tangent f L hL.le hd hgrad τ hsc μ hμ y z
  have hx : F y+inner ℝ w (s.1-y) ≤ F s.1 := by
    have ht := smoothing_strong_tangent f L hL.le hd hgrad τ hsc μ hμ y s.1
    have ht' : F y+inner ℝ w (s.1-y)+τ/2*‖s.1-y‖^2 ≤ F s.1 := ht
    have hpos := mul_nonneg (show 0≤τ/2 by positivity) (sq_nonneg ‖s.1-y‖)
    linarith only [ht', hpos]
  have hfinal := potential_integral_step (stdGaussian E) r hr hr2 F s.1 s.2 y z w
    g gp a τ l θ h (3*μ^2*L*((Module.finrank ℝ E:ℝ)+8)/16) (f z)
    hgp.le ha ha1 hl0 hl1 hs hleft hright hbalance hz hx hmean hdstep.1 hdstep.2
  simpa only [statePotential, nextState] using hfinal

end RandomGradFree.AcceleratedProof

end

/- Complete source body: AcceleratedObjective -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace RandomGradFree.AcceleratedProof
open RandomGradFree.Shared RandomGradFree.Accelerated

theorem accelerated_objective_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : 2 ≤ Module.finrank ℝ E) (f : E → ℝ) (L : ℝ) (hL : 0<L)
    (hd : Differentiable ℝ f) (hgrad : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (τ : ℝ) (hτ : 0≤τ)
    (hsc : ∀ x y, f x+inner ℝ (gradient f x) (y-x)+τ/2*‖y-x‖^2 ≤ f y)
    (z : E) (hopt : ∀ x, f z ≤ f x) (μ : ℝ) (hμ : 0≤μ)
    (θ h : ℝ) (hθ : θ=1/(16*((Module.finrank ℝ E:ℝ)+4)^2*L))
    (hh : h=1/(4*((Module.finrank ℝ E:ℝ)+4)*L))
    (x₀ : E) (γ α : ℕ → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u x v : ℕ → Ω → E)
    (hrun : IsAcceleratedRandomRun P f μ τ θ h x₀ γ α u x v) (k : ℕ) :
    (∫ ω, f (x k ω) ∂P)-f z ≤
      psi α k*(f x₀-f z+γ 0/2*‖x₀-z‖^2)+
      μ^2*L*((Module.finrank ℝ E:ℝ)+3*((Module.finrank ℝ E:ℝ)+8)/16*C α k) := by
  have hτL := tau_le_lipschitz (by omega : 0<Module.finrank ℝ E) f L τ hgrad hsc
  have hn : 0 ≤ (Module.finrank ℝ E:ℝ) := Nat.cast_nonneg _
  have hθp : 0<θ := by rw [hθ]; exact (theta_pos_and_small hn hL hτL).1
  have hθτ : θ*τ<1 := by rw [hθ]; exact (theta_pos_and_small hn hL hτL).2
  have hgb := coefficient_gamma_bounds hτ hθp hθτ γ α hrun.gamma_zero_pos
    hrun.tau_le_gamma_zero hrun.alpha_pos hrun.alpha_eq hrun.gamma_succ
  have ha1 := coefficient_alpha_lt_one hτ hθp hθτ γ α hrun.gamma_zero_pos
    hrun.tau_le_gamma_zero hrun.alpha_pos hrun.alpha_eq hrun.gamma_succ
  have hs (j : ℕ) : α j^2=θ*γ (j+1) := by
    apply coefficient_square hθp.ne' γ α _ j
    intro i
    rw [hrun.alpha_eq i, hrun.gamma_succ i]
  let F := smoothing f μ
  let δ := F z-f z
  let ξ := 3*μ^2*L*((Module.finrank ℝ E:ℝ)+8)/16
  let Q : ℕ → E × E → ℝ := fun j => statePotential F z (f z) (γ j)
  let K : ℕ → (E × E) × E → ℝ := fun j p =>
    Q (j+1) (nextState f μ τ (γ j) (γ (j+1)) (α j) θ h p.1 p.2)
  have hfconv := convex_of_strong_tangent f (gradient f) τ hτ hsc
  have hsb := smoothing_bounds f hfconv L hL.le hd hgrad μ hμ
  have hlower (a : E) : f z ≤ F a := (hopt a).trans (hsb a).1
  have hδ : 0≤δ := by dsimp [δ]; linarith [(hsb z).1]
  have hξ : 0≤ξ := by dsimp [ξ]; positivity
  have hFc : Continuous F := (smoothing_regular f L hL.le hd hgrad μ hμ).1.continuous
  have hoc := oracle_continuous f L μ hd hgrad
  have hQm (j : ℕ) : Measurable (Q j) := (statePotential_continuous F hFc z (f z) (γ j)).measurable
  have hQ0 (j : ℕ) (s : E × E) : 0≤Q j s :=
    statePotential_nonneg F z (f z) (γ j) (hgb j).1.le hlower s
  have hKm (j : ℕ) : Measurable (K j) :=
    (hQm (j+1)).comp (nextState_continuous f μ τ (γ j) (γ (j+1)) (α j) θ h hoc).measurable
  have hK0 (j : ℕ) (s : E × E) (d : E) : 0≤K j (s,d) := hQ0 (j+1) _
  have hfixed (j : ℕ) (s : E × E) := fixed_state_potential hdim f L hL hd hgrad τ hτ hsc
    z hopt μ hμ θ h hθ hh (γ j) (γ (j+1)) (α j) (hgb j).1 (hgb (j+1)).1
    (hrun.alpha_pos j) (ha1 j).le (hrun.gamma_succ j) (hs j) s
  have hKi (j : ℕ) (s : E × E) : Integrable (fun d => K j (s,d)) (stdGaussian E) :=
    (hfixed j s).1
  have hstep (j : ℕ) (ω : Ω) : Q (j+1) (x (j+1) ω,v (j+1) ω)=K j ((x j ω,v j ω),u j ω) := by
    rw [hrun.step_x j ω, hrun.step_v j ω]
    rfl
  have hbound (j : ℕ) (s : E × E) :
      (∫ d, K j (s,d) ∂stdGaussian E) ≤ (1-α j)*Q j s+(ξ+α j*δ) := by
    have ht := (hfixed j s).2
    change _ ≤ (1-α j)*Q j s+ξ+α j*δ at ht
    linarith
  have htransport := run_nonnegative_potential hoc hrun Q hQm hQ0 K hKm hK0 hKi hstep
    (fun j => 1-α j) (fun j => ξ+α j*δ) (fun j => (sub_pos.mpr (ha1 j)).le)
    (fun j => add_nonneg hξ (mul_nonneg (hrun.alpha_pos j).le hδ)) hbound
  let R : ℕ → ℝ := fun j => ∫ ω, Q j (x j ω,v j ω) ∂P
  have hrec (j : ℕ) : R (j+1) ≤ (1-α j)*R j+ξ+α j*δ := by
    have ht := htransport.2 j
    change R (j+1) ≤ (1-α j)*R j+(ξ+α j*δ) at ht
    linarith
  have hunroll := potential_recurrence_bound α R ξ δ (fun j => (ha1 j).le) hrec k
  have hstate := run_state_transport hoc hrun
  have hobjm : AEStronglyMeasurable (fun ω => f (x k ω)) P :=
    (hd.continuous.measurable.comp (hstate k).1.fst).aestronglyMeasurable
  have hupper (ω : Ω) : f (x k ω)-f z ≤ Q k (x k ω,v k ω) := by
    change _ ≤ γ k/2*‖v k ω-z‖^2+F (x k ω)-f z
    have hgk := (hgb k).1
    have hp := mul_nonneg (show 0≤γ k/2 by positivity) (sq_nonneg ‖v k ω-z‖)
    linarith [(hsb (x k ω)).1]
  have hobj := objective_integrable_of_potential (fun ω => f (x k ω))
    (fun ω => Q k (x k ω,v k ω)) (f z) hobjm (htransport.1 k) (fun ω => hopt _) hupper
  have hobjR : (∫ ω, f (x k ω) ∂P)-f z ≤ R k := hobj.2
  have hR0 : R 0=γ 0/2*‖x₀-z‖^2+F x₀-f z := by
    simp [R, Q, statePotential, hrun.init_x, hrun.init_v]
  let B := μ^2/2*L*(Module.finrank ℝ E:ℝ)
  have hB : 0≤B := by dsimp [B]; positivity
  have h0 : R 0 ≤ f x₀-f z+γ 0/2*‖x₀-z‖^2+B := by
    rw [hR0]
    have hb0 : F x₀-f x₀ ≤ B := (hsb x₀).2
    linarith only [hb0]
  have hδB : δ≤B := (hsb z).2
  have hψ : 0≤psi α k := (psi_pos α ha1 k).le
  have hψ1 : psi α k≤1 := psi_le_one α (fun j => (hrun.alpha_pos j).le) (fun j => (ha1 j).le) k
  have h0' := mul_le_mul_of_nonneg_left h0 hψ
  have hδ' := mul_le_mul_of_nonneg_right hδB (sub_nonneg.mpr hψ1)
  have hfinal : (∫ ω, f (x k ω) ∂P)-f z ≤
      psi α k*(f x₀-f z+γ 0/2*‖x₀-z‖^2)+2*B+ξ*C α k := by
    nlinarith [hobjR]
  have he : 2*B+ξ*C α k =
      μ^2*L*((Module.finrank ℝ E:ℝ)+3*((Module.finrank ℝ E:ℝ)+8)/16*C α k) := by
    dsimp [B, ξ]
    ring
  rwa [add_assoc, he] at hfinal

end RandomGradFree.AcceleratedProof

end

/- Complete source body: AcceleratedRoot -/
section

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem accelerated_random_method_rate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 < L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hsc : ∀ x y, f y ≥ f x + inner ℝ (gradient f x) (y - x) + τ / 2 * ‖y - x‖ ^ 2)
    (xstar : E) (hopt : ∀ y, f xstar ≤ f y)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (θ : ℝ) (hθ : θ = 1 / (16 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 * L₁))
    (h : ℝ) (hh : h = 1 / (4 * ((Module.finrank ℝ E : ℝ) + 4) * L₁))
    (x₀ : E) (γ α : ℕ → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u x v : ℕ → Ω → E) (hrun : IsAcceleratedRandomRun P f μ τ θ h x₀ γ α u x v) (k : ℕ) :
    (∫ ω, f (x k ω) ∂P) - f xstar
        ≤ psi α k * (f x₀ - f xstar + γ 0 / 2 * ‖x₀ - xstar‖ ^ 2)
          + μ ^ 2 * L₁ * ((Module.finrank ℝ E : ℝ)
            + 3 * ((Module.finrank ℝ E : ℝ) + 8) / 16 * C α k) ∧
      psi α k ≤ (1 - Real.sqrt (τ / L₁) / (4 * ((Module.finrank ℝ E : ℝ) + 4))) ^ k ∧
      psi α k ≤ 1 / (1 + k / (8 * ((Module.finrank ℝ E : ℝ) + 4)) * Real.sqrt (γ 0 / L₁)) ^ 2 ∧
      C α k ≤ k ∧
      (0 < τ → C α k ≤ 4 * ((Module.finrank ℝ E : ℝ) + 4) / Real.sqrt (τ / L₁)) := by
  have hsc' : ∀ x y, f x + inner ℝ (gradient f x) (y-x) + τ/2*‖y-x‖^2 ≤ f y := hsc
  have hτL := RandomGradFree.AcceleratedProof.tau_le_lipschitz
    (by omega : 0 < Module.finrank ℝ E) f L₁ τ hgrad hsc'
  have hrate := RandomGradFree.AcceleratedProof.coefficient_rate_bounds
    (Module.finrank ℝ E) L₁ τ θ hL₁ hτ hτL hθ γ α
    hrun.gamma_zero_pos hrun.tau_le_gamma_zero hrun.alpha_pos hrun.alpha_eq hrun.gamma_succ k
  exact ⟨RandomGradFree.AcceleratedProof.accelerated_objective_bound hdim f L₁ hL₁ hdiff hgrad
    τ hτ hsc' xstar hopt μ hμ θ h hθ hh x₀ γ α P u x v hrun k, hrate⟩

end RandomGradFree.Accelerated

end

end

open MeasureTheory ProbabilityTheory RandomGradFree.Accelerated

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 < L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hsc : ∀ x y, f y ≥ f x + inner ℝ (gradient f x) (y - x) + τ / 2 * ‖y - x‖ ^ 2)
    (xstar : E) (hopt : ∀ y, f xstar ≤ f y)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (θ : ℝ) (hθ : θ = 1 / (16 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 * L₁))
    (h : ℝ) (hh : h = 1 / (4 * ((Module.finrank ℝ E : ℝ) + 4) * L₁))
    (x₀ : E) (γ α : ℕ → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u x v : ℕ → Ω → E) (hrun : IsAcceleratedRandomRun P f μ τ θ h x₀ γ α u x v) (k : ℕ) :
    (∫ ω, f (x k ω) ∂P) - f xstar
        ≤ psi α k * (f x₀ - f xstar + γ 0 / 2 * ‖x₀ - xstar‖ ^ 2)
          + μ ^ 2 * L₁ * ((Module.finrank ℝ E : ℝ)
            + 3 * ((Module.finrank ℝ E : ℝ) + 8) / 16 * C α k) ∧
      psi α k ≤ (1 - Real.sqrt (τ / L₁) / (4 * ((Module.finrank ℝ E : ℝ) + 4))) ^ k ∧
      psi α k ≤ 1 / (1 + k / (8 * ((Module.finrank ℝ E : ℝ) + 4)) * Real.sqrt (γ 0 / L₁)) ^ 2 ∧
      C α k ≤ k ∧
      (0 < τ → C α k ≤ 4 * ((Module.finrank ℝ E : ℝ) + 4) / Real.sqrt (τ / L₁)) := by
  exact RandomGradFree.Accelerated.accelerated_random_method_rate hdim f L₁ hL₁ hdiff hgrad τ hτ hsc xstar hopt μ hμ θ hθ h hh x₀ γ α P u x v hrun k

#print axioms RandomGradFree.Accelerated.accelerated_random_method_rate
#print axioms solution
