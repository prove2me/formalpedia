-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P28.bayesian_loss
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:48:48.970453+00:00
-- url     : https://prove2.me/submissions/04ce26e6-3f5a-4ab1-ba07-9c7144c604e6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28
noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)


lemma g67h_quad_vec {I : Type*} [Fintype I] (G : HSMatrix I) (A : Op I) :
    representationQuadratic G A =
      (star (operatorCoordinates A) ⬝ᵥ (G *ᵥ operatorCoordinates A)).re := by
  simp only [representationQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    RCLike.star_def, mul_assoc]

lemma g67h_onOp {I : Type*} [Fintype I] (G : HSMatrix I) (A : Op I) :
    operatorCoordinates (onOperator G A) = G *ᵥ operatorCoordinates A := by
  funext p; simp [operatorCoordinates, onOperator, Matrix.mulVec, dotProduct]

lemma g67h_quadQ {I : Type*} [Fintype I] (G Q : HSMatrix I) (A : Op I) (hQ : Qᴴ = Q)
    (hA : onOperator Q A = A) :
    representationQuadratic (Q * G * Q) A = representationQuadratic G A := by
  have hv : Q *ᵥ operatorCoordinates A = operatorCoordinates A := by rw [← g67h_onOp, hA]
  have hs : star (operatorCoordinates A) ᵥ* Q = star (operatorCoordinates A) := by
    conv_lhs => rw [← hQ, ← Matrix.star_mulVec, hv]
  rw [g67h_quad_vec, g67h_quad_vec, ← Matrix.mulVec_mulVec, hv, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, hs]

lemma g67h_trace_onOp {I : Type*} [Fintype I] (Q : HSMatrix I) (R A : Op I) (hQ : Qᴴ = Q)
    (hR : Rᴴ = R) (hRQ : onOperator Q R = R) :
    (R * onOperator Q A).trace = (R * A).trace := by
  have hv : Q *ᵥ operatorCoordinates R = operatorCoordinates R := by rw [← g67h_onOp, hRQ]
  have key : ∀ q : I × I, ∑ p, R p.2 p.1 * Q p q = R q.2 q.1 := by
    intro q
    have h1 := congrFun hv q
    simp only [Matrix.mulVec, dotProduct, operatorCoordinates] at h1
    have hRe : ∀ i j, R j i = star (R i j) := fun i j => by
      conv_lhs => rw [← hR]
      exact Matrix.conjTranspose_apply R i j
    have hQe : ∀ p q, Q p q = star (Q q p) := fun p q => by
      conv_lhs => rw [← hQ]
      exact Matrix.conjTranspose_apply Q q p
    calc ∑ p, R p.2 p.1 * Q p q = star (∑ p, Q q p * R p.1 p.2) := by
          rw [star_sum]; refine Finset.sum_congr rfl fun p _ => ?_
          rw [star_mul', hRe p.1 p.2, hQe p q, mul_comm]
      _ = R q.2 q.1 := by rw [h1, ← hRe]
  calc (R * onOperator Q A).trace
      = ∑ q : I × I, (∑ p : I × I, R p.2 p.1 * Q p q) * A q.1 q.2 := by
        simp only [Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, onOperator]
    _ = (R * A).trace := by
        simp only [key, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
        rw [Finset.sum_comm]

lemma g67h_var {I X K : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace K]
    (mu : Measure X) (nu : Measure K) [SFinite mu] [SFinite nu]
    (P D : X → Op I) (R : K → Op I) (G : HSMatrix I)
    (hint : BayesianIntegrable mu nu P D R G) :
    ∫ k, bayesVariance mu P D (R k) G ∂nu =
      bayesEta mu P D (∫ k, R k ∂nu) G - ∫ k, representationQuadratic G (R k) ∂nu := by
  obtain ⟨hR, hq, hf, -⟩ := hint
  unfold bayesVariance
  have hf' : Integrable (fun k => bayesEta mu P D (R k) G) nu := hf.integral_prod_left
  rw [integral_sub hf' hq]
  congr 1
  unfold bayesEta
  rw [integral_integral_swap (f := fun k x => (P x * R k).trace.re * representationQuadratic G (D x)) hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_mul_const]
  congr 1
  let L : Op I →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap I ℂ ℂ).comp (LinearMap.mulLeft ℂ (P x)))
  have hL : ∀ M, L M = (P x * M).trace := fun _ => rfl
  have h1 := L.integral_comp_comm hR
  simp only [hL] at h1
  have h2 : Integrable (fun k => (P x * R k).trace) nu := by
    simpa [hL] using L.integrable_comp hR
  rw [← h1]
  exact integral_re h2

/-- PDF pp.1–2, (8)–(10),(19)–(20): arbitrary-prior Bayesian loss and subspace reduction.
The state and operation cases are kept as two physical alternatives. Projection changes the
estimator to the projected representation; it need not preserve an arbitrary unprojected dual's noise. -/
theorem solution {di do_ : ℕ} (hi : 0 < di) (ho : 0 < do_)
    {X K : Type*} [MeasurableSpace X] [MeasurableSpace K]
    (mu : Measure X) (nu : Measure K) [SFinite mu] [IsProbabilityMeasure nu]
    (P D : X → Op (Fin do_ × Fin di)) (R : K → Op (Fin do_ × Fin di))
    (V : Set (Op (Fin do_ × Fin di))) (G Q : HSMatrix (Fin do_ × Fin di))
    (hphysical : ((∀ k, QAlgorithms.IsDensityMatrix (R k)) ∧ IsPOVMDensity mu P) ∨
      ((∀ k, IsOperation (R k)) ∧ IsTesterDensity mu P))
    (hdual : IsTomographyDual mu P D V) (hsupport : ∀ k, R k ∈ V)
    (hG : G.PosSemidef) (hQ : Qᴴ = Q ∧ Q * Q = Q)
    (hQV : ∀ A, A ∈ V ↔ onOperator Q A = A)
    (hint : BayesianIntegrable mu nu P D R G)
    (hintQ : BayesianIntegrable mu nu P D R (Q * G * Q)) :
    BayesianReduction mu nu P D R G Q ∧
    (∀ k A, (R k * onOperator Q A).trace = (R k * A).trace) := by


  have hRQ : ∀ k, onOperator Q (R k) = R k := fun k => (hQV (R k)).1 (hsupport k)
  have hRh : ∀ k, (R k)ᴴ = R k := by
    intro k
    rcases hphysical with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (h1 k).1.isHermitian
    · exact (h1 k).1.isHermitian
  refine ⟨?_, fun k A => g67h_trace_onOp Q (R k) A hQ.1 (hRh k) (hRQ k)⟩
  simp only [BayesianReduction]
  refine ⟨g67h_var mu nu P D R G hint, ?_⟩
  rw [g67h_var mu nu P D R (Q * G * Q) hintQ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  exact g67h_quadQ G Q (R k) hQ.1 (hRQ k)
