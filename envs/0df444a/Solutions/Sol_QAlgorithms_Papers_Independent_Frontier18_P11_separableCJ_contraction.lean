-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P11.separableCJ_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T13:16:20.721513+00:00
-- url     : https://prove2.me/submissions/83f73b74-5616-45b1-ac28-529bf2fd4949

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11

set_option autoImplicit false

noncomputable section

open scoped TensorProduct ComplexOrder

namespace P9709Aux

open QAlgorithms.Papers.Independent.Frontier18.P11

lemma posOp_isPositive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (hT : positiveOperator T) : T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have h := hT x
  have h1 : inner ℂ (T x) x = (starRingEnd ℂ) (inner ℂ x (T x)) := (inner_conj_symm _ _).symm
  rw [h1]
  set z := inner ℂ x (T x) with hzdef
  have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h.1])
  rw [hz]
  simp [h.2]

lemma exists_sqrt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : positiveOperator T) :
    ∃ S : H →L[ℂ] H, (∀ x y, inner ℂ (S x) y = inner ℂ x (S y)) ∧ ∀ x, S (S x) = T x := by
  have h0 : (0 : H →L[ℂ] H) ≤ T :=
    (ContinuousLinearMap.nonneg_iff_isPositive T).2 (posOp_isPositive T hT)
  refine ⟨CFC.sqrt T, ?_, ?_⟩
  · have hs : IsSelfAdjoint (CFC.sqrt T) := (CFC.sqrt_nonneg T).isSelfAdjoint
    intro x y
    exact hs.isSymmetric x y
  · intro x
    have := CFC.sqrt_mul_sqrt_self T h0
    rw [← ContinuousLinearMap.mul_apply, this]

lemma inner_sqrt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S T : H →L[ℂ] H) (hS : ∀ x y, inner ℂ (S x) y = inner ℂ x (S y))
    (hST : ∀ x, S (S x) = T x) (x y : H) :
    inner ℂ x (T y) = inner ℂ (S x) (S y) := by
  rw [← hST, hS]

lemma density_le {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {I : Type*} (e : HilbertBasis I ℂ B) (ρ : B →L[ℂ] B) (h : densityOperator e ρ) (b : B) :
    (inner ℂ b (ρ b)).re ≤ ‖b‖ ^ 2 := by
  obtain ⟨S, hS, hST⟩ := exists_sqrt ρ h.1
  have hdiag : ∀ k, (inner ℂ (e k) (ρ (e k))).re = ‖S (e k)‖ ^ 2 := by
    intro k
    rw [inner_sqrt S ρ hS hST, inner_self_eq_norm_sq_to_K]
    norm_cast
  have h1 : HasSum (fun k => ‖S (e k)‖ ^ 2 * ‖b‖ ^ 2) (‖b‖ ^ 2) := by
    have := (h.2.mul_right (‖b‖ ^ 2))
    simp only [one_mul] at this
    refine this.congr_fun ?_
    intro k
    simp [hdiag k]
  set w := S b
  have h2 : HasSum (fun k => (inner ℂ w (e k) * inner ℂ (e k) w).re) (inner ℂ w w).re :=
    Complex.hasSum_re (e.hasSum_inner_mul_inner w w)
  have hle : ∀ k, (inner ℂ w (e k) * inner ℂ (e k) w).re ≤ ‖S (e k)‖ ^ 2 * ‖b‖ ^ 2 := by
    intro k
    have ha : ‖inner ℂ w (e k)‖ ≤ ‖b‖ * ‖S (e k)‖ := by
      rw [show inner ℂ w (e k) = inner ℂ b (S (e k)) from hS b (e k)]
      exact norm_inner_le_norm _ _
    have hb : ‖inner ℂ (e k) w‖ ≤ ‖S (e k)‖ * ‖b‖ := by
      rw [show inner ℂ (e k) w = inner ℂ (S (e k)) b from (hS (e k) b).symm]
      exact norm_inner_le_norm _ _
    calc (inner ℂ w (e k) * inner ℂ (e k) w).re ≤ ‖inner ℂ w (e k) * inner ℂ (e k) w‖ :=
          Complex.re_le_norm _
      _ = ‖inner ℂ w (e k)‖ * ‖inner ℂ (e k) w‖ := norm_mul _ _
      _ ≤ (‖b‖ * ‖S (e k)‖) * (‖S (e k)‖ * ‖b‖) :=
          mul_le_mul ha hb (norm_nonneg _) (by positivity)
      _ = ‖S (e k)‖ ^ 2 * ‖b‖ ^ 2 := by ring
  have h3 := hasSum_le hle h2 h1
  have h4 : (inner ℂ b (ρ b)).re = (inner ℂ w w).re := by
    rw [inner_sqrt S ρ hS hST]
  linarith

lemma one_sub_pos {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {I : Type*} (e : HilbertBasis I ℂ B) (ρ : B →L[ℂ] B) (h : densityOperator e ρ) :
    positiveOperator (1 - ρ) := by
  intro x
  have hx := h.1 x
  have hle := density_le e ρ h x
  have hself : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right, hself]
  constructor
  · simp only [Complex.sub_im, Complex.ofReal_im, hx.1, sub_zero]
  · simp only [Complex.sub_re, Complex.ofReal_re]
    linarith

lemma schur_nonneg {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace A] [CompleteSpace B]
    (P : B →L[ℂ] B) (Q : A →L[ℂ] A) (hP : positiveOperator P) (hQ : positiveOperator Q)
    (S : Finset (B × A)) :
    0 ≤ (∑ p ∈ S, ∑ q ∈ S, inner ℂ p.1 (P q.1) * inner ℂ p.2 (Q q.2)).re := by
  obtain ⟨C, hC, hCP⟩ := exists_sqrt P hP
  obtain ⟨D, hD, hDQ⟩ := exists_sqrt Q hQ
  set u : B ⊗[ℂ] A := ∑ p ∈ S, (C p.1) ⊗ₜ[ℂ] (D p.2) with hu
  have key : (∑ p ∈ S, ∑ q ∈ S, inner ℂ p.1 (P q.1) * inner ℂ p.2 (Q q.2)) = inner ℂ u u := by
    rw [hu, sum_inner]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [inner_sum]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [TensorProduct.inner_tmul, inner_sqrt C P hC hCP, inner_sqrt D Q hD hDQ]
  rw [key]
  have h := inner_self_nonneg (𝕜 := ℂ) (x := u)
  exact h

lemma coe_sum {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] (S : Finset (B × A)) :
    ((∑ p ∈ S, p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B) =
      ∑ p ∈ S, ((p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, UniformSpace.Completion.coe_add, ih]

lemma finite_le {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace A] [CompleteSpace B]
    {I : Type*} (e : HilbertBasis I ℂ B)
    (F : JointHilbert A B →L[ℂ] JointHilbert A B) (hF : finiteSeparableCJ e F)
    (t : B ⊗[ℂ] A) :
    (inner ℂ (t : JointHilbert A B) (F t)).re ≤ ‖(t : JointHilbert A B)‖ ^ 2 := by
  obtain ⟨n, rho, M, hrho, hM, hsum, hel⟩ := hF
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset t
  rw [coe_sum]
  set x : JointHilbert A B := ∑ p ∈ S, ((p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B) with hx
  have hFx : inner ℂ x (F x) =
      ∑ p ∈ S, ∑ q ∈ S, ∑ i, inner ℂ p.1 (rho i q.1) * inner ℂ p.2 (M i q.2) := by
    rw [hx, map_sum, sum_inner]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [inner_sum]
    refine Finset.sum_congr rfl ?_
    intro q _
    exact hel p.1 q.1 p.2 q.2
  have hMs : ∀ a a' : A, inner ℂ a a' = ∑ i, inner ℂ a (M i a') := by
    intro a a'
    rw [← inner_sum, ← ContinuousLinearMap.sum_apply, hsum]
    rfl
  have hxx : inner ℂ x x =
      ∑ p ∈ S, ∑ q ∈ S, ∑ i, inner ℂ p.1 q.1 * inner ℂ p.2 (M i q.2) := by
    rw [hx, sum_inner]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [inner_sum]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul, hMs, Finset.mul_sum]
  have hdiff : inner ℂ x x - inner ℂ x (F x) =
      ∑ i, ∑ p ∈ S, ∑ q ∈ S, inner ℂ p.1 ((1 - rho i) q.1) * inner ℂ p.2 (M i q.2) := by
    rw [hxx, hFx, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [← Finset.sum_sub_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right, sub_mul]
  have hnn : 0 ≤ (inner ℂ x x - inner ℂ x (F x)).re := by
    rw [hdiff, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ =>
      schur_nonneg (1 - rho i) (M i) (one_sub_pos e (rho i) (hrho i)) (hM i) S
  have hself : (inner ℂ x x).re = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [Complex.sub_re, hself] at hnn
  linarith

end P9709Aux

open QAlgorithms.Papers.Independent.Frontier18.P11 in
theorem solution {A B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [CompleteSpace A] [CompleteSpace B]
    [SecondCountableTopology A] [SecondCountableTopology B]
    {I : Type*} [Countable I] (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B) (hO : separableCJ e O) :
    ‖O‖ ≤ 1 := by
  obtain ⟨hpos, -, hcl⟩ := hO
  have hcoe : ∀ t : B ⊗[ℂ] A,
      (inner ℂ (t : JointHilbert A B) (O t)).re ≤ ‖(t : JointHilbert A B)‖ ^ 2 := by
    intro t
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨F, hF, hFt⟩ := hcl {((t : JointHilbert A B), (t : JointHilbert A B))} ε hε
    have hd := hFt _ (Finset.mem_singleton_self _)
    have h1 := P9709Aux.finite_le e F hF t
    have h2 : (inner ℂ (t : JointHilbert A B) (O t)).re -
        (inner ℂ (t : JointHilbert A B) (F t)).re ≤
        ‖inner ℂ (t : JointHilbert A B) (F t) - inner ℂ (t : JointHilbert A B) (O t)‖ := by
      rw [← norm_neg, neg_sub, ← Complex.sub_re]
      exact Complex.re_le_norm _
    simp only at hd
    linarith
  have hall : ∀ x : JointHilbert A B, (inner ℂ x (O x)).re ≤ ‖x‖ ^ 2 := by
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_le (by fun_prop) (by fun_prop)
    | ih t => exact hcoe t
  obtain ⟨S, hS, hSO⟩ := P9709Aux.exists_sqrt O hpos
  have hSn : ‖S‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound S zero_le_one fun x => ?_
    have h1 : ‖S x‖ ^ 2 = (inner ℂ x (O x)).re := by
      rw [P9709Aux.inner_sqrt S O hS hSO, inner_self_eq_norm_sq_to_K]; norm_cast
    have h2 : ‖S x‖ ^ 2 ≤ ‖x‖ ^ 2 := h1 ▸ hall x
    rw [one_mul]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hOc : O = S.comp S := by
    ext x
    exact (hSO x).symm
  rw [hOc]
  calc ‖S.comp S‖ ≤ ‖S‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 := mul_le_one₀ hSn (norm_nonneg _) hSn
