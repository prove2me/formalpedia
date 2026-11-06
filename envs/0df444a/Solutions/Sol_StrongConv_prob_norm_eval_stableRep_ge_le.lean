-- Prove2me | solution 1 for StrongConv.prob_norm_eval_stableRep_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:08:49.972656+00:00
-- url     : https://prove2.me/submissions/e90067e1-f8b9-48d5-bb19-f21eb84c7392

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_testFunction
import Theorems.Thm_StrongConv_exists_csDistribution_abs_stableExpTr_sub_le
import Theorems.Thm_StrongConv_supp_subset_Icc_of_stableExpTr_expansion
import Theorems.Thm_StrongConv_vanishesNear_supp

section
open scoped ComplexOrder
open Polynomial
open scoped InnerProductSpace

namespace StrongConv.Stable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma pow_apply_eigen (T : E →L[ℂ] E) (μ : ℂ) (v : E) (hv : T v = μ • v) (n : ℕ) :
    (T ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

lemma aeval_apply_eigen (T : E →L[ℂ] E) (μ : ℂ) (v : E) (hv : T v = μ • v) (q : ℂ[X]) :
    (Polynomial.aeval T q) v = q.eval μ • v := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a =>
    simp [Polynomial.aeval_monomial, pow_apply_eigen T μ v hv n, smul_smul, mul_comm]

lemma fnCalc_apply_eigenvector (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (χ : ℝ → ℝ)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ T) (v : E) (hv : T v = μ • v) :
    fnCalc χ T v = ((χ μ.re : ℝ) : ℂ) • v := by
  classical
  have hfin : (spectrum ℂ T).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]; exact Module.End.finite_spectrum _
  set s : Finset ℝ := hfin.toFinset.image Complex.re with hs
  set p : ℝ[X] := Lagrange.interpolate s id χ with hpdef
  have hp : ∀ z ∈ spectrum ℂ T, p.eval z.re = χ z.re := by
    intro z hz
    have hmem : z.re ∈ s := by
      rw [hs, Finset.mem_image]; exact ⟨z, hfin.mem_toFinset.mpr hz, rfl⟩
    have := Lagrange.eval_interpolate_at_node (s := s) (i := z.re) (v := id) χ
      (Set.injOn_id _) hmem
    simp only [id_eq] at this
    exact this
  have key : ∀ z ∈ spectrum ℂ T, (p.map (algebraMap ℝ ℂ)).eval z = ((χ z.re : ℝ) : ℂ) := by
    intro z hz
    have hzr := hT.mem_spectrum_eq_re hz
    conv_lhs => rw [hzr]
    rw [Polynomial.eval_map]
    have h0 : ((z.re : ℝ) : ℂ) = algebraMap ℝ ℂ z.re := rfl
    rw [h0, Polynomial.eval₂_at_apply, hp z hz]
    rfl
  have h1 : fnCalc χ T = Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) := by
    unfold fnCalc
    rw [← cfc_polynomial (R := ℂ) (p.map (algebraMap ℝ ℂ)) T]
    exact cfc_congr (fun z hz => (key z hz).symm)
  rw [h1, aeval_apply_eigen T μ v hv, key μ hμ]

lemma fnCalc_nonneg (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (χ : ℝ → ℝ) (hχ : ∀ x, 0 ≤ χ x) :
    0 ≤ fnCalc χ T := by
  unfold fnCalc
  apply cfc_nonneg
  intro x _
  exact_mod_cast hχ x.re


lemma one_le_re_trace_fnCalc (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (χ : ℝ → ℝ)
    (hχ0 : ∀ x, 0 ≤ χ x) (c : ℝ) (hc : 0 < c) (hχ1 : ∀ x, c ≤ |x| → χ x = 1)
    (hTc : c ≤ ‖T‖) :
    1 ≤ (LinearMap.trace ℂ E ((fnCalc χ T : E →L[ℂ] E) : E →ₗ[ℂ] E)).re := by
  classical
  have hT0 : T ≠ 0 := by
    rintro rfl; simp at hTc; linarith
  have : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hT0 (Subsingleton.elim _ _)
  have hne : (spectrum ℂ T).Nonempty := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ T
  obtain ⟨μ, hμ, hμn⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hne
  rw [hT.spectralRadius_eq_nnnorm] at hμn
  have hμnorm : ‖μ‖ = ‖T‖ := by
    simpa using congrArg ((↑) : NNReal → ℝ) (ENNReal.coe_inj.mp hμn)
  have hμre : μ = (μ.re : ℂ) := hT.mem_spectrum_eq_re hμ
  have habs : c ≤ |μ.re| := by
    have : ‖μ‖ = |μ.re| := by
      conv_lhs => rw [hμre]
      simp
    linarith
  have hμ' : μ ∈ spectrum ℂ (T : E →ₗ[ℂ] E) := by
    rwa [ContinuousLinearMap.spectrum_eq] at hμ
  obtain ⟨v0, hv0⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ').exists_hasEigenvector
  have hv0T : T v0 = μ • v0 := Module.End.mem_eigenspace_iff.mp hv0.1
  have hv0ne : v0 ≠ 0 := hv0.2
  set v : E := (‖v0‖⁻¹ : ℂ) • v0 with hvdef
  have hnorm0 : ‖v0‖ ≠ 0 := norm_ne_zero_iff.mpr hv0ne
  have hvnorm : ‖v‖ = 1 := by
    rw [hvdef, norm_smul]; simp [hnorm0]
  have hvT : T v = μ • v := by
    rw [hvdef, map_smul, hv0T, smul_comm]
  set S := fnCalc χ T with hS
  have hSv : S v = ((χ μ.re : ℝ) : ℂ) • v := fnCalc_apply_eigenvector T hT χ μ hμ v hvT
  have hSpos : S.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive S).mp
    (fnCalc_nonneg T hT χ hχ0)
  have hone : χ μ.re = 1 := hχ1 _ habs
  have hon : Orthonormal ℂ ((↑) : ({v} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro x hx y hy
    have hx' : x = v := hx
    have hy' : y = v := hy
    subst hx'; subst hy'
    simp [inner_self_eq_norm_sq_to_K, hvnorm]
  obtain ⟨u, b, hub, hb⟩ := hon.exists_orthonormalBasis_extension
  rw [LinearMap.trace_eq_sum_inner _ b]
  rw [Complex.re_sum]
  have hmem : (⟨v, hub (Set.mem_singleton v)⟩ : u) ∈ (Finset.univ : Finset u) := Finset.mem_univ _
  calc (1 : ℝ) = (⟪b ⟨v, hub (Set.mem_singleton v)⟩, S (b ⟨v, hub (Set.mem_singleton v)⟩)⟫_ℂ).re := by
        have : b ⟨v, hub (Set.mem_singleton v)⟩ = v := by
          have := congrFun hb ⟨v, hub (Set.mem_singleton v)⟩
          simpa using this
        rw [this, hSv, hone]
        simp [inner_smul_right, inner_self_eq_norm_sq_to_K, hvnorm]
    _ ≤ _ := by
        apply Finset.single_le_sum (f := fun i : u => (⟪b i, S (b i)⟫_ℂ).re) _ hmem
        intro i _
        exact hSpos.re_inner_nonneg_right (b i)


lemma re_trace_fnCalc_nonneg (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (χ : ℝ → ℝ)
    (hχ0 : ∀ x, 0 ≤ χ x) :
    0 ≤ (LinearMap.trace ℂ E ((fnCalc χ T : E →L[ℂ] E) : E →ₗ[ℂ] E)).re := by
  classical
  have hSpos : (fnCalc χ T).IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (fnCalc_nonneg T hT χ hχ0)
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E), Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hSpos.re_inner_nonneg_right _

end StrongConv.Stable
end

section
namespace StrongConv.Stable

lemma rpow_inv_le_exp {x b : ℝ} (hx : 1 ≤ x) (hb : b = 1 + Real.log x) :
    x ^ (1 / b) ≤ Real.exp 1 := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hb0 : 0 < b := by rw [hb]; linarith
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  rw [mul_one_div, div_le_one hb0]
  rw [hb]; linarith

lemma final_ineq (α m : ℕ) (hm : m = 4 * (α + 1)) (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (D q ℓ K ε N L : ℝ) (hD : 0 ≤ D) (hq : 0 ≤ q) (hℓ : Real.log 2 ≤ ℓ) (hε : 0 < ε)
    (hεK : ε < K) (hN : 1 ≤ N) (hL0 : 0 ≤ L)
    (hL : L ≤ (A₂ * m) ^ m * (2 * (K / ε)) ^ ((m : ℝ) + 1 / (1 + Real.log (2 * (K / ε))))) :
    N ^ α * (A₁ * D * (q * (1 + ℓ)) ^ m / N ^ (α + 1) * (1 + Real.log (2 * (K / ε))) * L) ≤
      (A₁ * (2 * (1 + 1 / Real.log 2) * A₂ * m) ^ m * Real.exp 1 * (1 + Real.log 2)) * D / N *
        (K * q * ℓ / ε) ^ m * Real.log (Real.exp 1 * K / ε) := by
  set t : ℝ := K / ε with ht
  have ht1 : 1 < t := by rw [ht, lt_div_iff₀ hε]; linarith
  have ht0 : 0 < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1.le
  have hN0 : 0 < N := by linarith
  set b : ℝ := 1 + Real.log (2 * t) with hb
  have hlog2t : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht0.ne'
  have hb' : b = 1 + Real.log (2 * t) := rfl
  have h2t1 : 1 ≤ 2 * t := by linarith
  have hb0 : 0 < b := by rw [hb']; have := Real.log_nonneg h2t1; linarith
  -- bound on the rpow
  have hrp : (2 * t) ^ ((m : ℝ) + 1 / b) ≤ (2 * t) ^ m * Real.exp 1 := by
    rw [Real.rpow_add (by linarith), Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (rpow_inv_le_exp h2t1 hb') (by positivity)
  have hL' : L ≤ (A₂ * m) ^ m * ((2 * t) ^ m * Real.exp 1) :=
    hL.trans (mul_le_mul_of_nonneg_left hrp (by positivity))
  have hb2 : b ≤ (1 + Real.log 2) * (1 + Real.log t) := by
    rw [hb', hlog2t]; nlinarith
  have hℓ' : 1 + ℓ ≤ (1 + 1 / Real.log 2) * ℓ := by
    have : 1 ≤ ℓ / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
    have h3 : 1 / Real.log 2 * ℓ = ℓ / Real.log 2 := by field_simp
    nlinarith
  have hlog_e : Real.log (Real.exp 1 * K / ε) = 1 + Real.log t := by
    rw [mul_div_assoc, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, ← ht]
  have hα : N ^ α / N ^ (α + 1) = 1 / N := by
    rw [pow_succ]; field_simp
  have hq1 : 0 ≤ q * (1 + ℓ) := by
    have : 0 ≤ ℓ := hlog2.le.trans hℓ
    positivity
  have hq2 : (q * (1 + ℓ)) ^ m ≤ (q * ((1 + 1 / Real.log 2) * ℓ)) ^ m :=
    pow_le_pow_left₀ hq1 (mul_le_mul_of_nonneg_left hℓ' hq) m
  have hb0' : 0 ≤ b := hb0.le
  calc N ^ α * (A₁ * D * (q * (1 + ℓ)) ^ m / N ^ (α + 1) * b * L)
      = (A₁ * D / N) * (q * (1 + ℓ)) ^ m * b * L := by
        have : N ^ α * (A₁ * D * (q * (1 + ℓ)) ^ m / N ^ (α + 1) * b * L) =
            (N ^ α / N ^ (α + 1)) * (A₁ * D * (q * (1 + ℓ)) ^ m * b * L) := by ring
        rw [this, hα]; ring
    _ ≤ (A₁ * D / N) * (q * ((1 + 1 / Real.log 2) * ℓ)) ^ m *
          ((1 + Real.log 2) * (1 + Real.log t)) * ((A₂ * m) ^ m * ((2 * t) ^ m * Real.exp 1)) := by
        have hD' : 0 ≤ A₁ * D / N := by positivity
        have hlogℓ : 0 ≤ ℓ := hlog2.le.trans hℓ
        gcongr
    _ = (A₁ * (2 * (1 + 1 / Real.log 2) * A₂ * m) ^ m * Real.exp 1 * (1 + Real.log 2)) * D / N *
        (K * q * ℓ / ε) ^ m * Real.log (Real.exp 1 * K / ε) := by
        rw [hlog_e]
        have : (K * q * ℓ / ε) = t * q * ℓ := by rw [ht]; ring
        rw [this]
        have e1 : (q * ((1 + 1 / Real.log 2) * ℓ)) ^ m * ((A₂ * m) ^ m * (2 * t) ^ m) =
            (2 * (1 + 1 / Real.log 2) * A₂ * m) ^ m * (t * q * ℓ) ^ m := by
          rw [← mul_pow, ← mul_pow, ← mul_pow]; congr 1; ring
        calc (A₁ * D / N) * (q * ((1 + 1 / Real.log 2) * ℓ)) ^ m *
              ((1 + Real.log 2) * (1 + Real.log t)) * ((A₂ * m) ^ m * ((2 * t) ^ m * Real.exp 1))
            = (A₁ * D / N) * ((1 + Real.log 2) * (1 + Real.log t)) * Real.exp 1 *
              ((q * ((1 + 1 / Real.log 2) * ℓ)) ^ m * ((A₂ * m) ^ m * (2 * t) ^ m)) := by ring
          _ = _ := by rw [e1]; ring

end StrongConv.Stable
end

section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv.Stable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (y : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    tensorOp A T y a = ∑ b, A a b • T (y b) := by
  unfold tensorOp
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.single_apply,
    PiLp.proj_apply, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_sum, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, Pi.smul_apply, Pi.single_apply]
  simp [Finset.sum_comm (γ := Fin n)]

lemma inner_tensorOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin m => H)) (y : PiLp 2 (fun _ : Fin n => H)) :
    ⟪x, tensorOp A T y⟫_ℂ = ∑ a, ∑ b, A a b * ⟪x a, T (y b)⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensorOp_apply, inner_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_smul_right]

lemma star_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    star (tensorOp A T) = tensorOp Aᴴ (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- ⟪tensorOp Aᴴ T† x, y⟫ = ⟪x, tensorOp A T y⟫
  rw [inner_tensorOp, ← inner_conj_symm, inner_tensorOp, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, inner_conj_symm]
  simp only [Matrix.conjTranspose_apply, star_star, Complex.star_def]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp only [Complex.conj_conj]

lemma star_letterOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (l : Fin d ⊕ Fin d) :
    star (letterOp u l) = letterOp u l.swap := by
  rcases l with i | i <;> simp [letterOp]

lemma star_list_prod' {A : Type*} [Monoid A] [StarMul A] (l : List A) :
    star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, star_mul]

lemma star_wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    star (wordOp u w) = wordOp u (NCPoly.wordStar w) := by
  unfold wordOp NCPoly.wordStar
  rw [star_list_prod']
  simp only [FreeMonoid.toList_ofList, List.map_map, List.map_reverse]
  congr 1
  congr 1
  apply List.map_congr_left
  intro l _
  simp [star_letterOp]

lemma wordStar_wordStar {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (NCPoly.wordStar w) = w := by
  unfold NCPoly.wordStar
  apply FreeMonoid.toList.injective
  simp [Function.comp_def]

lemma isSelfAdjoint_eval {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (P.eval u) := by
  classical
  have hsupp : ∀ w, w ∈ P.support ↔ NCPoly.wordStar w ∈ P.support := by
    intro w
    simp only [Finsupp.mem_support_iff]
    rw [hP w]
    simp
  unfold IsSelfAdjoint NCPoly.eval
  have hs : star (∑ w ∈ P.support, tensorOp (P w) (wordOp u w)) =
      ∑ w ∈ P.support, star (tensorOp (P w) (wordOp u w)) := by
    simp only [ContinuousLinearMap.star_eq_adjoint]
    exact map_sum ContinuousLinearMap.adjoint _ _
  rw [hs]
  simp only [star_tensorOp, star_wordOp]
  refine Finset.sum_equiv ⟨NCPoly.wordStar, NCPoly.wordStar, wordStar_wordStar,
    wordStar_wordStar⟩ ?_ ?_
  · intro w
    simp only [Equiv.coe_fn_mk]
    exact hsupp w
  · intro w hw
    simp only [Equiv.coe_fn_mk]
    rw [← hP w]

end StrongConv.Stable
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.Stable

lemma uniformProb_le_uniformExp {X : Type*} [Fintype X] [Nonempty X] (E : X → Prop) (f : X → ℝ)
    (h1 : ∀ x, E x → 1 ≤ f x) (hf : ∀ x, 0 ≤ f x) : uniformProb E ≤ uniformExp f := by
  classical
  unfold uniformProb uniformExp
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  apply div_le_div_of_nonneg_right _ hc.le
  calc ((Finset.univ.filter E).card : ℝ) = ∑ x ∈ Finset.univ.filter E, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ Finset.univ.filter E, f x := Finset.sum_le_sum fun x hx => h1 x (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => hf x

lemma uniformExp_div {X : Type*} [Fintype X] (f : X → ℝ) (c : ℝ) :
    uniformExp (fun x => f x / c) = uniformExp f / c := by
  unfold uniformExp; rw [← Finset.sum_div, div_div, div_div, mul_comm]


end StrongConv.Stable

namespace StrongConv

open StrongConv.Stable
open Matrix

theorem prob_norm_eval_stableRep_ge_le_dev (π : StableRep) (hπ : π.NoTrivialSummand) :
    ∃ C : ℝ, ∀ D d q₀ : ℕ, 2 ≤ d → ∀ P : NCPoly D d, P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∀ ε : ℝ, 0 < ε → ε < P.fullNorm - ‖P.eval (sLimit d)‖ → ∀ N : ℕ, π.N₀ ≤ N →
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖P.eval (sLimit d)‖ + ε ≤ ‖P.eval (π.model σ)‖) ≤
        C * D / N * (P.fullNorm * q₀ * Real.log d / ε) ^ (4 * (π.alpha + 1)) *
          Real.log (Real.exp 1 * P.fullNorm / ε) := by
  obtain ⟨C₁, hC₁⟩ := exists_csDistribution_abs_stableExpTr_sub_le π
  obtain ⟨C₂, hC₂⟩ := exists_testFunction
  set m : ℕ := 4 * (π.alpha + 1) with hm
  have hm1 : 1 ≤ m := by omega
  refine ⟨max C₁ 0 * (2 * (1 + 1 / Real.log 2) * |C₂| * m) ^ m * Real.exp 1 *
    (1 + Real.log 2), ?_⟩
  intro D d q₀ hd P hP hq ε hε hεK N hN
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd'
  set K := P.fullNorm with hKdef
  set ρ := ‖P.eval (sLimit d)‖ with hρdef
  have hρ : 0 ≤ ρ := norm_nonneg _
  have hKε : ρ + ε < K := by linarith
  have hKpos : 0 < K := by linarith
  by_cases hN0 : N = 0
  · -- the event is empty: for `N = 0` there are no nonzero fixed vectors, so the space is zero
    subst hN0
    have hdim : π.dim 0 = 0 := by
      by_contra hne
      have hpos : 0 < π.dim 0 := Nat.pos_of_ne_zero hne
      have hfix : ∀ σ : Equiv.Perm (Fin 0),
          (π.π 0 σ : Matrix (Fin (π.dim 0)) (Fin (π.dim 0)) ℂ) *ᵥ (fun _ => (1 : ℂ)) =
            fun _ => (1 : ℂ) := by
        intro σ
        have : σ = 1 := Subsingleton.elim _ _
        subst this
        simp
      have h0 := hπ 0 hN _ hfix
      have := congrFun h0 ⟨0, hpos⟩
      simp at this
    have hempty : ∀ σ : Fin d → Equiv.Perm (Fin 0), ¬ (ρ + ε ≤ ‖P.eval (π.model σ)‖) := by
      intro σ hle
      have hsub : Subsingleton (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim 0)))) := by
        rw [hdim]; infer_instance
      have : P.eval (π.model σ) = 0 := by
        exact ContinuousLinearMap.ext fun x => Subsingleton.elim _ _
      rw [this, norm_zero] at hle
      linarith
    have : uniformProb (fun σ : Fin d → Equiv.Perm (Fin 0) => ρ + ε ≤ ‖P.eval (π.model σ)‖) = 0 := by
      unfold uniformProb
      classical
      simp [Finset.filter_eq_empty_iff.mpr (fun σ _ => hempty σ)]
    rw [this]
    simp
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  obtain ⟨χ, hχs, hχ01, hχ0, hχ1, hχlp⟩ := hC₂ m K (ρ + ε / 2) (ε / 2) hm1 hKpos
    (by positivity) (by positivity) (by linarith)
  obtain ⟨ν, hνcs, hνexp⟩ := hC₁ hd P hP hq
  have hexp : ∀ h : ℝ[X], ∃ C : ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
      |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((fnCalc (fun x => h.eval x) (P.eval (π.model σ)) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
            (N : ℝ) ^ π.alpha) -
        ∑ i ∈ Finset.range (π.alpha + 1), ν i (polyFun h) / (N : ℝ) ^ i| ≤
        C / (N : ℝ) ^ (π.alpha + 1) := by
    intro h
    refine ⟨C₁ * D * (q₀ * (1 + Real.log d)) ^ m * conjExp 2 *
      lpNormCircle 2 (iteratedDeriv (m + 1) (fun θ => ((polyFun h : smoothFun) : ℝ → ℝ)
        (K * Real.cos θ))), fun N hN hN1 => ?_⟩
    have := hνexp N hN hN1 2 (by norm_num) (polyFun h)
    refine this.trans (le_of_eq ?_)
    ring
  have hsupp := supp_subset_Icc_of_stableExpTr_expansion π hπ hd P hP ν hνcs hexp
  have hχv : ∀ i ≤ π.alpha, ν i ⟨χ, hχs⟩ = 0 := by
    intro i hi
    apply vanishesNear_supp (ν i) (hνcs i) ⟨χ, hχs⟩
    rw [Filter.eventually_iff, mem_nhdsSet_iff_exists]
    refine ⟨Metric.ball 0 (ρ + ε / 2), Metric.isOpen_ball, ?_, ?_⟩
    · intro x hx
      have := hsupp i hi hx
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      rcases this with ⟨h1, h2⟩
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · intro x hx
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
      exact hχ0 x (by linarith)
  set b : ℝ := 1 + Real.log (2 * (K / ε)) with hbdef
  have hKe : 1 < K / ε := by rw [lt_div_iff₀ hε]; linarith
  have hb1 : 1 < b := by
    have : 0 < Real.log (2 * (K / ε)) := Real.log_pos (by linarith)
    rw [hbdef]; linarith
  set β : ℝ := b / (b - 1) with hβdef
  have hβ : 1 < β := by
    rw [hβdef, lt_div_iff₀ (by linarith)]; linarith
  have hconj : conjExp β = b := by
    unfold conjExp
    rw [hβdef]
    have : b - 1 ≠ 0 := by linarith
    have hb0 : b ≠ 0 := by linarith
    field_simp
    ring
  have key := hνexp N hN hN1 β hβ ⟨χ, hχs⟩
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [hχv i (by have := Finset.mem_range.mp hi; omega)]; simp), sub_zero, hconj] at key
  set L := lpNormCircle β (iteratedDeriv (4 * (π.alpha + 1) + 1)
    (fun θ => ((⟨χ, hχs⟩ : smoothFun) : ℝ → ℝ) (K * Real.cos θ))) with hLdef
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hL : L ≤ (|C₂| * m) ^ m * (2 * (K / ε)) ^ ((m : ℝ) + 1 / (1 + Real.log (2 * (K / ε)))) := by
    have h1 := hχlp β hβ
    rw [hconj] at h1
    have h2 : K / (ε / 2) = 2 * (K / ε) := by field_simp
    rw [h2] at h1
    have h3 : (C₂ * m) ^ m ≤ (|C₂| * m) ^ m :=
      calc (C₂ * m) ^ m ≤ |(C₂ * m) ^ m| := le_abs_self _
        _ = (|C₂| * m) ^ m := by rw [abs_pow, abs_mul, Nat.abs_cast]
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by positivity) _))
  -- probability bound by the trace of the test function
  have hprob := uniformProb_le_uniformExp
    (fun σ : Fin d → Equiv.Perm (Fin N) => ρ + ε ≤ ‖P.eval (π.model σ)‖)
    (fun σ : Fin d → Equiv.Perm (Fin N) =>
      (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
        ((fnCalc χ (P.eval (π.model σ)) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re)
    (fun σ hσ => one_le_re_trace_fnCalc _
      (isSelfAdjoint_eval P hP (π.model σ)) χ (fun x => (hχ01 x).1)
      (ρ + ε) (by linarith) (fun x hx => hχ1 x (by linarith)) hσ)
    (fun σ => re_trace_fnCalc_nonneg _
      (isSelfAdjoint_eval P hP (π.model σ)) χ (fun x => (hχ01 x).1))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNα : (0 : ℝ) < (N : ℝ) ^ π.alpha := by positivity
  have hfe := uniformExp_div (fun σ : Fin d → Equiv.Perm (Fin N) =>
      (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
        ((fnCalc χ (P.eval (π.model σ)) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re) ((N : ℝ) ^ π.alpha)
  rw [eq_div_iff hNα.ne'] at hfe
  have hA₁ : C₁ ≤ max C₁ 0 := le_max_left _ _
  have hX : 0 ≤ (q₀ * (1 + Real.log d)) ^ m := by
    have : 0 ≤ Real.log d := (Real.log_nonneg (by linarith))
    positivity
  have hb0 : 0 ≤ b := by linarith
  have hbound : (N : ℝ) ^ π.alpha * |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
        ((fnCalc χ (P.eval (π.model σ)) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
        (N : ℝ) ^ π.alpha)| ≤ (N : ℝ) ^ π.alpha *
      (max C₁ 0 * D * (q₀ * (1 + Real.log d)) ^ m / (N : ℝ) ^ (π.alpha + 1) * b * L) := by
    apply mul_le_mul_of_nonneg_left _ hNα.le
    refine key.trans ?_
    gcongr
  have hfin := final_ineq π.alpha m hm (max C₁ 0) |C₂| (le_max_right _ _) (abs_nonneg _) D q₀
    (Real.log d) K ε N L (Nat.cast_nonneg D) (Nat.cast_nonneg q₀) hlog2 hε (by linarith)
    (by exact_mod_cast hN1) hL0 hL
  refine hprob.trans ?_
  refine le_trans ?_ (hbound.trans hfin)
  rw [← hfe, mul_comm]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) hNα.le

end StrongConv
end
end

theorem solution : type_of% @StrongConv.prob_norm_eval_stableRep_ge_le_dev := @StrongConv.prob_norm_eval_stableRep_ge_le_dev
