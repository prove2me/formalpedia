-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.gaussian_cq_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T01:03:06.302607+00:00
-- url     : https://prove2.me/submissions/7b5c3b97-7bd3-4c54-9364-8713294c01b5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_isCQ_of_weyl_dual_commutes

noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction
open scoped Matrix RealInnerProductSpace InnerProductSpace

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (ScaledWeylRepresentation InterleavedPhase physicalCommutationMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

private abbrev Om (s : ℕ) : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ :=
  physicalCommutationMatrix s 1

private lemma phaseArgument_add {s : ℕ} (z w : InterleavedPhase s) :
    QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (z + w) =
      QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z +
        QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 w := by
  funext i
  cases i <;> simp [QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument]

private lemma phaseArgument_smul {s : ℕ} (r : ℝ) (z : InterleavedPhase s) :
    QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (r • z) =
      r • QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z := by
  funext i
  cases i <;> simp [QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument]

private lemma operator_mul {I : Type} {s : ℕ} (W : ScaledWeylRepresentation I s 1)
    (z w : InterleavedPhase s) :
    W.operator z * W.operator w =
      Complex.exp (Complex.I * (QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
        (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z)
        (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 w) : ℂ) / 2) •
        W.operator (z + w) := by
  rw [ContinuousLinearMap.mul_def]
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.comp_apply, smul_apply]
  change (W.normalized.operator (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z))
      ((W.normalized.operator (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 w)) u) =
    Complex.exp (Complex.I * (QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z)
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 w) : ℂ) / 2) •
      (W.normalized.operator (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (z + w))) u
  rw [QAlgorithms.Papers.Independent.Frontier30.P10.WeylSystem.multiply]
  congr 2
  rw [phaseArgument_add]

private lemma symplecticPair_smul_left {s : ℕ} (r : ℝ)
    (z w : QAlgorithms.Papers.Independent.Dependency50.P10.Phase s → ℝ) :
    QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair (r • z) w =
      r * QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair z w := by
  simp only [QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  congr 1
  ext j
  ring

private lemma symplecticPair_smul_right {s : ℕ} (r : ℝ)
    (z w : QAlgorithms.Papers.Independent.Dependency50.P10.Phase s → ℝ) :
    QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair z (r • w) =
      r * QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair z w := by
  simp only [QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  congr 1
  ext j
  ring

private lemma symplecticPair_skew {s : ℕ}
    (z w : QAlgorithms.Papers.Independent.Dependency50.P10.Phase s → ℝ) :
    QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair z w =
      - QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair w z := by
  simp only [QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair]
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext j
  ring

private lemma lp_single_ne_zero {I : Type} [Nonempty I] [DecidableEq I] (i : I) :
    (lp.single 2 i (1 : ℂ) : Hilbert I) ≠ 0 := by
  intro h
  have hnorm : ‖(lp.single 2 i (1 : ℂ) : Hilbert I)‖ = 1 := by
    rw [lp.norm_single (p := (2 : ℝ≥0∞)) (by norm_num)]
    norm_num
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

private lemma operator_ne_zero {I : Type} [Nonempty I] {s : ℕ}
    (W : ScaledWeylRepresentation I s 1) (z : InterleavedPhase s) :
    W.operator z ≠ 0 := by
  classical
  intro h0
  obtain ⟨i⟩ := ‹Nonempty I›
  let v : Hilbert I := lp.single 2 i (1 : ℂ)
  have hv : v ≠ 0 := lp_single_ne_zero i
  have hz : W.operator z v = 0 := by rw [h0]; rfl
  have hcoe : W.operator z v = (W.normalized.operator
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z)) v := rfl
  rw [hcoe] at hz
  exact hv ((W.normalized.operator
    (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z)).injective (by simpa using hz))

private lemma weyl_commute_of_symplectic_zero {I : Type} {s : ℕ}
    (W : ScaledWeylRepresentation I s 1) (z w : InterleavedPhase s)
    (hθ : QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z)
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 w) = 0) :
    W.operator z * W.operator w = W.operator w * W.operator z := by
  rw [operator_mul, operator_mul, hθ, symplecticPair_skew, hθ]
  simp only [Complex.ofReal_zero, mul_zero, zero_div, Complex.exp_zero, one_smul,
    neg_zero]
  rw [add_comm]

private lemma smul_comp_smul_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (a b : ℂ) (f g : E →L[ℂ] E) :
    (a • f).comp (b • g) = (a * b) • (f.comp g) := by
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  simp [smul_smul]

private lemma smul_comp_smul_eq' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (a b : ℂ) (f g : E →L[ℂ] E) :
    (b • g).comp (a • f) = (a * b) • (g.comp f) := by
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  simp [smul_smul, mul_comm]

private lemma symplectic_zero_of_weyl_commute_range {I : Type} [Nonempty I]
    {s t : ℕ} (W : ScaledWeylRepresentation I s 1)
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (hcomm : ∀ z w : InterleavedPhase t,
      W.operator (K.mulVec z) * W.operator (K.mulVec w) =
      W.operator (K.mulVec w) * W.operator (K.mulVec z))
    (z w : InterleavedPhase t) :
    QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec z))
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec w)) = 0 := by
  classical
  by_contra hθ
  let θ : ℝ := QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
    (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec z))
    (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec w))
  let r : ℝ := Real.pi / θ
  have hr : r * θ = Real.pi := by
    rw [show r = Real.pi / θ by rfl]
    field_simp [hθ]
    exact mul_inv_cancel₀ hθ
  have hcomm' := hcomm (r • z) w
  rw [Matrix.mulVec_smul] at hcomm'
  rw [operator_mul, operator_mul] at hcomm'
  rw [phaseArgument_smul] at hcomm'
  rw [symplecticPair_smul_left, symplecticPair_smul_right] at hcomm'
  rw [symplecticPair_skew (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec w))
    (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec z))] at hcomm'
  have hL : r * QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec z))
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec w)) = Real.pi := hr
  have hR : r * -QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec z))
      (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec w)) = -Real.pi := by
    rw [mul_neg, hr]
  rw [hL, hR, add_comm (r • K.mulVec z) (K.mulVec w)] at hcomm'
  have hI : (Complex.I : ℂ) • W.operator (K.mulVec w + r • K.mulVec z) =
      (-Complex.I) • W.operator (K.mulVec w + r • K.mulVec z) := by
    rw [show Complex.I * (Real.pi : ℂ) / 2 = Real.pi / 2 * Complex.I by ring,
      show Complex.I * (↑(-Real.pi) : ℂ) / 2 = -Real.pi / 2 * Complex.I by
        push_cast
        ring,
      Complex.exp_pi_div_two_mul_I, Complex.exp_neg_pi_div_two_mul_I] at hcomm'
    simpa [neg_smul] using hcomm'
  have hzero : ((2 : ℂ) * Complex.I) • W.operator (K.mulVec w + r • K.mulVec z) = 0 := by
    have hsub : (Complex.I : ℂ) • W.operator (K.mulVec w + r • K.mulVec z) -
        (-Complex.I) • W.operator (K.mulVec w + r • K.mulVec z) = 0 := sub_eq_zero.mpr hI
    rw [← sub_smul] at hsub
    have hcoef : (Complex.I : ℂ) - (-Complex.I) = 2 * Complex.I := by ring
    rw [hcoef] at hsub
    exact hsub
  rcases smul_eq_zero.mp hzero with hc | hW
  · norm_num at hc
  · exact operator_ne_zero W (K.mulVec w + r • K.mulVec z) hW

private lemma dotProduct_commMatrix (s : ℕ) (z w : InterleavedPhase s) :
    dotProduct z ((physicalCommutationMatrix s 1).mulVec w) =
      - QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
        (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 z)
        (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 w) := by
  simp only [dotProduct, Matrix.mulVec, physicalCommutationMatrix,
    QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair,
    QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num
  try
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring

private lemma matrix_eq_zero_of_dot (s t : ℕ)
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (h : ∀ z w : QuadratureIndex t → ℝ,
      dotProduct (K.mulVec z) ((Om s).mulVec (K.mulVec w)) = 0) :
    K.transpose * Om s * K = 0 := by
  classical
  ext j i
  have hji := h (Pi.single j 1) (Pi.single i 1)
  simp only [Matrix.mulVec_single_one] at hji
  simp only [dotProduct, Matrix.mulVec, Matrix.col_apply, Finset.mul_sum] at hji
  have hgoal : (K.transpose * Om s * K) j i =
      ∑ b, ∑ a, K b j * (K a i * Om s b a) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hgoal]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hji

private lemma dot_eq_zero_of_matrix_zero (s t : ℕ)
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (hK : K.transpose * Om s * K = 0) (z w : QuadratureIndex t → ℝ) :
    dotProduct (K.mulVec z) ((Om s).mulVec (K.mulVec w)) = 0 := by
  calc
    dotProduct (K.mulVec z) ((Om s).mulVec (K.mulVec w))
        = (K.mulVec z) ᵥ* (Om s) ⬝ᵥ (K.mulVec w) := by
          rw [Matrix.dotProduct_mulVec]
    _ = (z ᵥ* (Kᵀ * Om s)) ⬝ᵥ (K.mulVec w) := by
          rw [Matrix.vecMul_mulVec]
    _ = z ⬝ᵥ ((Kᵀ * Om s) *ᵥ (K.mulVec w)) := by
          exact (Matrix.dotProduct_mulVec z (Kᵀ * Om s) (K.mulVec w)).symm
    _ = z ⬝ᵥ (((Kᵀ * Om s) * K) *ᵥ w) := by
          congr 1
          exact Matrix.mulVec_mulVec w (Kᵀ * Om s) K
    _ = 0 := by rw [hK]; simp

private lemma weyl_commute_of_isCQ {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ)
    (hG : GaussianChannel WA WB Phi K alpha) (hCQ : IsCQ Phi)
    (z w : InterleavedPhase t) :
    WA.operator (K.mulVec z) * WA.operator (K.mulVec w) =
      WA.operator (K.mulVec w) * WA.operator (K.mulVec z) := by
  have hdual := hG.2.2.2
  have h := hCQ (WB.operator z) (WB.operator w)
  rw [hdual z, hdual w] at h
  rw [smul_comp_smul_eq, smul_comp_smul_eq'] at h
  have hcz : Complex.exp (-(dotProduct z (alpha.mulVec z) / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.exp_ne_zero _
  have hcw : Complex.exp (-(dotProduct w (alpha.mulVec w) / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.exp_ne_zero _
  have hcancel : (WA.operator (K.mulVec z)).comp (WA.operator (K.mulVec w)) =
      (WA.operator (K.mulVec w)).comp (WA.operator (K.mulVec z)) := by
    refine (smul_right_inj (mul_ne_zero hcz hcw)).mp ?_
    simpa using h
  simpa [ContinuousLinearMap.mul_def] using hcancel

end QAlgorithms.Papers.Independent.Next46.P18

open QAlgorithms.Papers.Independent.Next46.P18

theorem solution {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) (hG : GaussianChannel WA WB Phi K alpha) :
    IsCQ Phi ↔ K.transpose * (physicalCommutationMatrix s 1) * K = 0 := by
  constructor
  · intro hCQ
    apply matrix_eq_zero_of_dot s t K
    intro z w
    have hcommK : ∀ u v : InterleavedPhase t,
        WA.operator (K.mulVec u) * WA.operator (K.mulVec v) =
        WA.operator (K.mulVec v) * WA.operator (K.mulVec u) := by
      intro u v
      exact weyl_commute_of_isCQ WA WB Phi K alpha hG hCQ u v
    have hzero := symplectic_zero_of_weyl_commute_range WA K hcommK z w
    rw [dotProduct_commMatrix]
    simpa using hzero
  · intro hK
    apply isCQ_of_weyl_dual_commutes WB Phi
    intro z w
    have hdual := hG.2.2.2
    have hθ : QAlgorithms.Papers.Independent.Frontier30.P10.symplecticPair
        (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec z))
        (QAlgorithms.Papers.Independent.Claimed50.P35.phaseArgument 1 (K.mulVec w)) = 0 := by
      have hdot := dot_eq_zero_of_matrix_zero s t K hK z w
      rw [dotProduct_commMatrix] at hdot
      linarith
    rw [hdual z, hdual w, smul_comp_smul_eq, smul_comp_smul_eq']
    have hAB := weyl_commute_of_symplectic_zero WA (K.mulVec z) (K.mulVec w) hθ
    have hAB' : (WA.operator (K.mulVec z)).comp (WA.operator (K.mulVec w)) =
        (WA.operator (K.mulVec w)).comp (WA.operator (K.mulVec z)) := by
      simpa [ContinuousLinearMap.mul_def] using hAB
    rw [hAB']



end
