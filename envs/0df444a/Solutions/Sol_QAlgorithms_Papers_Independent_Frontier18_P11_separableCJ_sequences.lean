-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P11.separableCJ_sequences
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:03:47.408978+00:00
-- url     : https://prove2.me/submissions/54a8e4ff-4dbc-4beb-a07f-4e13ad96c39e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11

noncomputable section
open scoped TensorProduct ComplexOrder InnerProductSpace

namespace X5CJ
open QAlgorithms.Papers.Independent.Frontier18.P11

lemma pos_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (h : positiveOperator T) : 0 ≤ T := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  obtain ⟨h1, h2⟩ := h x
  have hc : ⟪T x, x⟫_ℂ = (starRingEnd ℂ) ⟪x, T x⟫_ℂ := (inner_conj_symm _ _).symm
  rw [hc]
  refine ⟨?_, by rw [RCLike.conj_re]; exact h2⟩
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.conj_re]
    rw [RCLike.conj_re]; rfl
  · simp only [Complex.ofReal_im, Complex.conj_im, h1, neg_zero]

/-- symmetric square root identity -/
lemma sqrt_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (x y : H) :
    ⟪x, T y⟫_ℂ = ⟪CFC.sqrt T x, CFC.sqrt T y⟫_ℂ := by
  have hs : IsSelfAdjoint (CFC.sqrt T) := (CFC.sqrt_nonneg T).isSelfAdjoint
  conv_lhs => rw [← CFC.sqrt_mul_sqrt_self T hT]
  show ⟪x, CFC.sqrt T (CFC.sqrt T y)⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  congr 1
  have : ContinuousLinearMap.adjoint (CFC.sqrt T) = CFC.sqrt T := hs
  rw [this]

lemma density_le {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {I : Type*} (e : HilbertBasis I ℂ B) (rho : B →L[ℂ] B) (h : densityOperator e rho) (b : B) :
    (⟪b, rho b⟫_ℂ).re ≤ ‖b‖ ^ 2 := by
  have h0 := pos_nonneg rho h.1
  set S := CFC.sqrt rho
  have hb : (⟪b, rho b⟫_ℂ).re = ‖S b‖ ^ 2 := by
    rw [sqrt_inner rho h0, inner_self_eq_norm_sq_to_K]; norm_cast
  have hs : IsSelfAdjoint S := (CFC.sqrt_nonneg rho).isSelfAdjoint
  have hadj : ∀ x y, ⟪x, S y⟫_ℂ = ⟪S x, y⟫_ℂ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_left]
    have : ContinuousLinearMap.adjoint S = S := hs
    rw [this]
  -- Parseval
  have hP : HasSum (fun i => ‖⟪e i, S b⟫_ℂ‖ ^ 2) (‖S b‖ ^ 2) := by
    have := (e.hasSum_inner_mul_inner (S b) (S b)).mapL Complex.reCLM
    convert this using 1
    · ext i
      simp only [Complex.reCLM_apply]
      rw [← inner_conj_symm (S b) (e i), Complex.conj_mul']
      norm_cast
    · simp only [Complex.reCLM_apply]
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hD : HasSum (fun i => ‖S (e i)‖ ^ 2 * ‖b‖ ^ 2) (1 * ‖b‖ ^ 2) := by
    have := h.2.mul_right (‖b‖ ^ 2)
    have hf : (fun i => (⟪e i, rho (e i)⟫_ℂ).re * ‖b‖ ^ 2) = (fun i => ‖S (e i)‖ ^ 2 * ‖b‖ ^ 2) := by
      funext i
      rw [sqrt_inner rho h0, inner_self_eq_norm_sq_to_K]; norm_cast
    rwa [hf] at this
  rw [hb]
  have := hasSum_le (fun i => ?_) hP hD
  · linarith
  · rw [hadj, ← mul_pow]
    gcongr
    exact norm_inner_le_norm _ _

end X5CJ


noncomputable section
open scoped TensorProduct ComplexOrder InnerProductSpace

namespace X5CJ
open QAlgorithms.Papers.Independent.Frontier18.P11

variable {A B : Type*}
variable [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
variable [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

lemma gram (P : B →L[ℂ] B) (Q : A →L[ℂ] A) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (S : Finset (B × A)) :
    (∑ p ∈ S, ∑ q ∈ S, ⟪p.1, P q.1⟫_ℂ * ⟪p.2, Q q.2⟫_ℂ) =
      ⟪∑ p ∈ S, CFC.sqrt P p.1 ⊗ₜ[ℂ] CFC.sqrt Q p.2,
        ∑ p ∈ S, CFC.sqrt P p.1 ⊗ₜ[ℂ] CFC.sqrt Q p.2⟫_ℂ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [TensorProduct.inner_tmul, sqrt_inner P hP, sqrt_inner Q hQ]

lemma gram_pos (P : B →L[ℂ] B) (Q : A →L[ℂ] A) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (S : Finset (B × A)) :
    (∑ p ∈ S, ∑ q ∈ S, ⟪p.1, P q.1⟫_ℂ * ⟪p.2, Q q.2⟫_ℂ).im = 0 ∧
    0 ≤ (∑ p ∈ S, ∑ q ∈ S, ⟪p.1, P q.1⟫_ℂ * ⟪p.2, Q q.2⟫_ℂ).re := by
  rw [gram P Q hP hQ S]
  exact ⟨inner_self_im (𝕜 := ℂ) (E := B ⊗[ℂ] A) _, inner_self_nonneg (𝕜 := ℂ) (E := B ⊗[ℂ] A)⟩

lemma pos_of_dense (T : JointHilbert A B →L[ℂ] JointHilbert A B)
    (h : ∀ t : B ⊗[ℂ] A, (⟪(t : JointHilbert A B), T t⟫_ℂ).im = 0 ∧
      0 ≤ (⟪(t : JointHilbert A B), T t⟫_ℂ).re) : positiveOperator T := by
  intro x
  refine UniformSpace.Completion.induction_on x ?_ h
  have hc : Continuous fun x : JointHilbert A B => ⟪x, T x⟫_ℂ :=
    continuous_id.inner T.continuous
  exact (isClosed_eq (Complex.continuous_im.comp hc) continuous_const).inter
    (isClosed_le continuous_const (Complex.continuous_re.comp hc))

lemma coe_sum (S : Finset (B × A)) :
    ((∑ p ∈ S, p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B) =
      ∑ p ∈ S, ((p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B) := by
  rw [← UniformSpace.Completion.coe_toComplₗᵢ (𝕜 := ℂ), map_sum]

lemma quad {I : Type*} (e : HilbertBasis I ℂ B) (F : JointHilbert A B →L[ℂ] JointHilbert A B)
    (n : ℕ) (rho : Fin n → B →L[ℂ] B) (M : Fin n → A →L[ℂ] A)
    (hel : ∀ (b b' : B) (a a' : A),
      inner ℂ (↑(b ⊗ₜ[ℂ] a) : JointHilbert A B)
        (F (↑(b' ⊗ₜ[ℂ] a') : JointHilbert A B)) =
        ∑ i, inner ℂ b (rho i b') * inner ℂ a (M i a')) (S : Finset (B × A)) :
    ⟪((∑ p ∈ S, p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B),
      F ((∑ p ∈ S, p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B)⟫_ℂ =
      ∑ i, ∑ p ∈ S, ∑ q ∈ S, ⟪p.1, rho i q.1⟫_ℂ * ⟪p.2, M i q.2⟫_ℂ := by
  simp only [coe_sum, map_sum, sum_inner, inner_sum, hel]
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun p _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

lemma norm_quad (S : Finset (B × A)) :
    ⟪((∑ p ∈ S, p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B),
      ((∑ p ∈ S, p.1 ⊗ₜ[ℂ] p.2 : B ⊗[ℂ] A) : JointHilbert A B)⟫_ℂ =
      ∑ p ∈ S, ∑ q ∈ S, ⟪p.1, q.1⟫_ℂ * ⟪p.2, q.2⟫_ℂ := by
  rw [UniformSpace.Completion.inner_coe, sum_inner]
  simp_rw [inner_sum, TensorProduct.inner_tmul]

theorem fsep_bound {I : Type*} (e : HilbertBasis I ℂ B)
    (F : JointHilbert A B →L[ℂ] JointHilbert A B) (hF : finiteSeparableCJ e F) : ‖F‖ ≤ 1 := by
  obtain ⟨n, rho, M, hrho, hM, hsum, hel⟩ := hF
  have hM0 : ∀ i, 0 ≤ M i := fun i => pos_nonneg _ (hM i)
  have hr0 : ∀ i, 0 ≤ rho i := fun i => pos_nonneg _ (hrho i).1
  have hr1 : ∀ i, 0 ≤ 1 - rho i := by
    intro i
    apply pos_nonneg
    intro b
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
      Complex.sub_im, Complex.sub_re, inner_self_im, (hrho i).1 b |>.1, sub_zero, sub_nonneg]
    have := density_le e (rho i) (hrho i) b
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hpos : positiveOperator F := by
    apply pos_of_dense
    intro t
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset t
    rw [quad e F n rho M hel S, Complex.im_sum, Complex.re_sum]
    exact ⟨Finset.sum_eq_zero fun i _ => (gram_pos _ _ (hr0 i) (hM0 i) S).1,
      Finset.sum_nonneg fun i _ => (gram_pos _ _ (hr0 i) (hM0 i) S).2⟩
  have hle : positiveOperator (1 - F) := by
    apply pos_of_dense
    intro t
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset t
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right]
    rw [quad e F n rho M hel S, norm_quad]
    have hid : ∀ a a' : A, ∑ i, ⟪a, M i a'⟫_ℂ = ⟪a, a'⟫_ℂ := by
      intro a a'
      rw [← inner_sum, ← ContinuousLinearMap.sum_apply, hsum]; rfl
    have e1 : (∑ p ∈ S, ∑ q ∈ S, ⟪p.1, q.1⟫_ℂ * ⟪p.2, q.2⟫_ℂ) =
        ∑ i, ∑ p ∈ S, ∑ q ∈ S, ⟪p.1, q.1⟫_ℂ * ⟪p.2, M i q.2⟫_ℂ := by
      refine Eq.trans ?_ Finset.sum_comm
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Eq.trans ?_ Finset.sum_comm
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.mul_sum, hid]
    have key : ∀ i, (∑ p ∈ S, ∑ q ∈ S, ⟪p.1, q.1⟫_ℂ * ⟪p.2, M i q.2⟫_ℂ) -
        ∑ p ∈ S, ∑ q ∈ S, ⟪p.1, rho i q.1⟫_ℂ * ⟪p.2, M i q.2⟫_ℂ =
        ∑ p ∈ S, ∑ q ∈ S, ⟪p.1, (1 - rho i) q.1⟫_ℂ * ⟪p.2, M i q.2⟫_ℂ := by
      intro i
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
        sub_mul]
    rw [e1, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun i _ => key i, Complex.im_sum, Complex.re_sum]
    exact ⟨Finset.sum_eq_zero fun i _ => (gram_pos _ _ (hr1 i) (hM0 i) S).1,
      Finset.sum_nonneg fun i _ => (gram_pos _ _ (hr1 i) (hM0 i) S).2⟩
  have h0 : 0 ≤ F := pos_nonneg F hpos
  have h1 : F ≤ 1 := by
    rw [← sub_nonneg]; exact pos_nonneg _ hle
  calc ‖F‖ ≤ ‖(1 : JointHilbert A B →L[ℂ] JointHilbert A B)‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 h1
    _ ≤ 1 := ContinuousLinearMap.norm_id_le

end X5CJ


noncomputable section
open scoped TensorProduct ComplexOrder InnerProductSpace
open Filter Topology TopologicalSpace

namespace X5CJ
open QAlgorithms.Papers.Independent.Frontier18.P11

lemma sep_tensor {A B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [SeparableSpace A] [SeparableSpace B] : SeparableSpace (B ⊗[ℂ] A) := by
  have hs : IsSeparable (Set.range fun x : B × A => x.1 ⊗ₜ[ℂ] x.2) :=
    isSeparable_range (TensorProduct.continuous_tmul (𝕜 := ℂ))
  have h2 := hs.span (R := ℂ)
  have he : (Set.range fun x : B × A => x.1 ⊗ₜ[ℂ] x.2) = { t | ∃ m n, m ⊗ₜ[ℂ] n = t } := by
    ext t; simp
  rw [he, TensorProduct.span_tmul_eq_top] at h2
  exact isSeparable_univ_iff.1 (by simpa using h2)

lemma approx {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : ℝ) (hK : 0 ≤ K) (x y : H) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x' y' : H, ‖x - x'‖ < δ → ‖y - y'‖ < δ → ∀ G : H →L[ℂ] H, ‖G‖ ≤ K →
      ‖⟪x, G y⟫_ℂ - ⟪x', G y'⟫_ℂ‖ < ε := by
  set c := ‖x‖ + ‖y‖ + 1
  have hc : 0 < c := by positivity
  set δ := min 1 (ε / (K * c + 1))
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ * (K * c + 1) ≤ ε := by
    have := min_le_right 1 (ε / (K * c + 1))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  refine ⟨δ, hδ, fun x' y' hx hy G hG => ?_⟩
  have hsplit : ⟪x, G y⟫_ℂ - ⟪x', G y'⟫_ℂ = ⟪x - x', G y⟫_ℂ + ⟪x', G (y - y')⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]; ring
  rw [hsplit]
  have h1 : ‖⟪x - x', G y⟫_ℂ‖ ≤ ‖x - x'‖ * (K * ‖y‖) := by
    refine (norm_inner_le_norm _ _).trans ?_
    gcongr
    exact (G.le_opNorm y).trans (by gcongr)
  have h2 : ‖⟪x', G (y - y')⟫_ℂ‖ ≤ ‖x'‖ * (K * ‖y - y'‖) := by
    refine (norm_inner_le_norm _ _).trans ?_
    gcongr
    exact (G.le_opNorm _).trans (by gcongr)
  have hx' : ‖x'‖ ≤ ‖x‖ + δ := by
    have := norm_sub_norm_le x' x
    rw [norm_sub_rev] at this; linarith
  have h3 : ‖x - x'‖ * (K * ‖y‖) ≤ δ * (K * ‖y‖) := by gcongr
  have h4 : ‖x'‖ * (K * ‖y - y'‖) ≤ (‖x‖ + δ) * (K * δ) := by
    gcongr
  have h5 : δ * (K * ‖y‖) + (‖x‖ + δ) * (K * δ) ≤ δ * (K * c) := by
    have : (‖x‖ + δ) * (K * δ) ≤ (‖x‖ + 1) * (K * δ) := by gcongr
    nlinarith
  calc ‖⟪x - x', G y⟫_ℂ + ⟪x', G (y - y')⟫_ℂ‖ ≤ _ := norm_add_le _ _
    _ ≤ δ * (K * c) := by linarith
    _ < ε := by nlinarith

lemma tri (a b c d : ℂ) : ‖a - d‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d‖ := by
  calc ‖a - d‖ ≤ ‖a - c‖ + ‖c - d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d‖ := by
      gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem main {A B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [CompleteSpace A] [CompleteSpace B]
    [SecondCountableTopology A] [SecondCountableTopology B]
    {I : Type*} [Countable I] (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B)
    (hO : positiveOperator O) (hMarginal : inputMarginal e O)
    (D : Submodule ℂ (JointHilbert A B)) (hD : Dense (D : Set (JointHilbert A B))) :
    separableCJ e O ↔
      ∃ F : ℕ → (JointHilbert A B →L[ℂ] JointHilbert A B),
        (∀ n, finiteSeparableCJ e (F n)) ∧
        ∀ x ∈ D, ∀ y ∈ D,
          Filter.Tendsto (fun n => inner ℂ x (F n y)) Filter.atTop
            (nhds (inner ℂ x (O y))) := by
  classical
  set K := max 1 ‖O‖
  have hK0 : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  have hKF : ∀ F, finiteSeparableCJ e F → ‖F‖ ≤ K :=
    fun F hF => (fsep_bound (A := A) e F hF).trans (le_max_left _ _)
  have hKO : ‖O‖ ≤ K := le_max_right _ _
  constructor
  · rintro ⟨-, -, hW⟩
    haveI : SeparableSpace (B ⊗[ℂ] A) := sep_tensor
    obtain ⟨s, hs⟩ := exists_dense_seq (JointHilbert A B)
    have hex : ∀ n : ℕ, ∃ F, finiteSeparableCJ e F ∧ ∀ i < n, ∀ j < n,
        ‖⟪s i, F (s j)⟫_ℂ - ⟪s i, O (s j)⟫_ℂ‖ < 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨F, hF, h⟩ := hW ((Finset.range n ×ˢ Finset.range n).image
        (fun ij => (s ij.1, s ij.2))) (1 / ((n : ℝ) + 1)) (by positivity)
      refine ⟨F, hF, fun i hi j hj => ?_⟩
      have hm : (s i, s j) ∈ (Finset.range n ×ˢ Finset.range n).image
          (fun ij : ℕ × ℕ => (s ij.1, s ij.2)) :=
        Finset.mem_image.2 ⟨(i, j), Finset.mem_product.2 ⟨Finset.mem_range.2 hi,
          Finset.mem_range.2 hj⟩, rfl⟩
      exact h (s i, s j) hm
    choose F hF hFt using hex
    refine ⟨F, hF, ?_⟩
    intro x _ y _
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := approx K hK0 x y (ε / 3) (by positivity)
    obtain ⟨i, hi⟩ := hs.exists_dist_lt x hδ
    obtain ⟨j, hj⟩ := hs.exists_dist_lt y hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
    refine ⟨max N (max i j + 1), fun n hn => ?_⟩
    rw [dist_eq_norm]
    rw [dist_eq_norm] at hi hj
    have h1 := hδ' (s i) (s j) hi hj (F n) (hKF _ (hF n))
    have h2 := hδ' (s i) (s j) hi hj O hKO
    have h3 := hFt n i (by omega) j (by omega)
    have h4 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : N ≤ n := le_trans (le_max_left _ _) hn
      exact_mod_cast Nat.add_le_add_right this 1
    have := tri ⟪x, F n y⟫_ℂ ⟪s i, F n (s j)⟫_ℂ ⟪s i, O (s j)⟫_ℂ ⟪x, O y⟫_ℂ
    rw [norm_sub_rev ⟪s i, O (s j)⟫_ℂ] at this
    linarith
  · rintro ⟨F, hF, hconv⟩
    refine ⟨hO, hMarginal, ?_⟩
    intro tests ε hε
    have hev : ∀ p ∈ tests, ∀ᶠ n in atTop, ‖⟪p.1, F n p.2⟫_ℂ - ⟪p.1, O p.2⟫_ℂ‖ < ε := by
      intro p _
      obtain ⟨δ, hδ, hδ'⟩ := approx K hK0 p.1 p.2 (ε / 3) (by positivity)
      obtain ⟨x', hx'D, hx'⟩ := hD.exists_dist_lt p.1 hδ
      obtain ⟨y', hy'D, hy'⟩ := hD.exists_dist_lt p.2 hδ
      rw [dist_eq_norm] at hx' hy'
      have hc := Metric.tendsto_nhds.1 (hconv x' hx'D y' hy'D) (ε / 3) (by positivity)
      filter_upwards [hc] with n hn
      rw [dist_eq_norm] at hn
      have h1 := hδ' x' y' hx' hy' (F n) (hKF _ (hF n))
      have h2 := hδ' x' y' hx' hy' O hKO
      have := tri ⟪p.1, F n p.2⟫_ℂ ⟪x', F n y'⟫_ℂ ⟪x', O y'⟫_ℂ ⟪p.1, O p.2⟫_ℂ
      rw [norm_sub_rev ⟪x', O y'⟫_ℂ] at this
      linarith
    obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset tests).2 hev).exists
    exact ⟨F n, hF n, hn⟩

end X5CJ

open scoped TensorProduct ComplexOrder in
open QAlgorithms.Papers.Independent.Frontier18.P11 in
theorem solution {A B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [CompleteSpace A] [CompleteSpace B]
    [SecondCountableTopology A] [SecondCountableTopology B]
    {I : Type*} [Countable I] (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B)
    (hO : positiveOperator O) (hMarginal : inputMarginal e O)
    (D : Submodule ℂ (JointHilbert A B)) (hD : Dense (D : Set (JointHilbert A B))) :
    separableCJ e O ↔
      ∃ F : ℕ → (JointHilbert A B →L[ℂ] JointHilbert A B),
        (∀ n, finiteSeparableCJ e (F n)) ∧
        ∀ x ∈ D, ∀ y ∈ D,
          Filter.Tendsto (fun n => inner ℂ x (F n y)) Filter.atTop
            (nhds (inner ℂ x (O y))) :=
  X5CJ.main e O hO hMarginal D hD
