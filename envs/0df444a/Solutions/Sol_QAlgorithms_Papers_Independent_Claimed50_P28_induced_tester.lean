-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P28.induced_tester
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:42:58.496988+00:00
-- url     : https://prove2.me/submissions/f4ed2683-37fb-4fb0-bf4e-8d9c7998261c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28
noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- `inducedTester rho` as a linear map. -/
def g67h_T {O I A : Type*} [Fintype A] (rho : Op (I × A)) :
    Op (O × A) →ₗ[ℂ] Op (O × I) where
  toFun := inducedTester rho
  map_add' P Q := by
    ext p q; simp [inducedTester, mul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    ext p q; simp [inducedTester, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => ?_
    refine Finset.sum_congr rfl fun _ _ => ?_; ring

lemma g67h_T_psd {O I A : Type*} [Fintype O] [Fintype I] [Fintype A]
    (rho : Op (I × A)) (P : Op (O × A)) (hr : rho.PosSemidef) (hP : P.PosSemidef) :
    (inducedTester rho P).PosSemidef := by
  let L : Matrix ((I × A) × (O × A)) (O × I) ℂ :=
    Matrix.of fun u v => if u.1.1 = v.2 ∧ u.2.1 = v.1 ∧ u.1.2 = u.2.2 then 1 else 0
  have hM : (Matrix.kronecker rho.transpose P).PosSemidef := hr.transpose.kronecker hP
  have h := hM.conjTranspose_mul_mul_same L
  convert h using 1
  refine Matrix.ext fun p q => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, L, Matrix.of_apply, Matrix.kronecker_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type]
  unfold inducedTester
  simp only [apply_ite, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply]

lemma g67h_reorder {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] (f : α → β → γ → δ → ε → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ d, ∑ b, ∑ e, ∑ a, ∑ c, f a b c d e := by
  calc _ = ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, ∑ e, f a b c d e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, ∑ e, f a b c d e := Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ a, ∑ c, ∑ e, f a b c d e :=
        Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ a, ∑ e, ∑ c, f a b c d e :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm

lemma g67h_trace_id {O I A : Type*} [Fintype O] [Fintype I] [Fintype A]
    (R : Op (O × I)) (rho : Op (I × A)) (P : Op (O × A)) :
    (applyWithAncilla R rho * P).trace = (R * inducedTester rho P).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, applyWithAncilla, inducedTester,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [g67h_reorder]
  simp only [mul_assoc]
/-- PDF p.2, (11)–(15): a normalized preparation and POVM induce a physical tester,
with exactly the original, possibly subnormalized, operation statistics. -/
theorem solution {di do_ : ℕ} (hi : 0 < di) (ho : 0 < do_)
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (rho : Op (Fin di × Fin di)) (P : X → Op (Fin do_ × Fin di))
    (hrho : QAlgorithms.IsDensityMatrix rho) (hP : IsPOVMDensity mu P) :
    IsTesterDensity mu (fun x => inducedTester rho (P x)) ∧
    (∫ x, inducedTester rho (P x) ∂mu) =
      Matrix.kronecker (1 : Op (Fin do_)) (traceInput rho).transpose ∧
    ∀ R : Op (Fin do_ × Fin di), IsOperation R → ∀ x,
      (applyWithAncilla R rho * P x).trace = (R * inducedTester rho (P x)).trace := by


  obtain ⟨hPi, hPpsd, hP1⟩ := hP
  let Tc := LinearMap.toContinuousLinearMap (g67h_T (O := Fin do_) rho)
  have hTc : ∀ M, Tc M = inducedTester rho M := fun _ => rfl
  have hint : Integrable (fun x => inducedTester rho (P x)) mu := by
    have := Tc.integrable_comp hPi
    simpa [hTc] using this
  have hInt : (∫ x, inducedTester rho (P x) ∂mu) =
      Matrix.kronecker (1 : Op (Fin do_)) (traceInput rho).transpose := by
    have := Tc.integral_comp_comm hPi
    simp only [hTc] at this
    rw [this, hP1]
    refine Matrix.ext fun p q => ?_
    simp only [inducedTester, Matrix.one_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, traceInput, Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero]
    by_cases h : p.1 = q.1
    · simp [h, Finset.sum_ite_eq]
    · simp [h]
  have hsig : QAlgorithms.IsDensityMatrix (traceInput rho).transpose := by
    constructor
    · have h1 : (inducedTester rho (1 : Op (Fin do_ × Fin di))).PosSemidef :=
        g67h_T_psd rho _ hrho.1 Matrix.PosSemidef.one
      have h2 : inducedTester rho (1 : Op (Fin do_ × Fin di)) =
          Matrix.kronecker (1 : Op (Fin do_)) (traceInput rho).transpose := by
        refine Matrix.ext fun p q => ?_
        simp only [inducedTester, Matrix.one_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.transpose_apply, traceInput, Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero]
        by_cases h : p.1 = q.1
        · simp [h, Finset.sum_ite_eq]
        · simp [h]
      rw [h2] at h1
      have h3 := h1.submatrix (fun i : Fin di => ((⟨0, ho⟩ : Fin do_), i))
      convert h3 using 1
      refine Matrix.ext fun i j => ?_
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
    · rw [Matrix.trace_transpose]
      have := hrho.2
      simp only [Matrix.trace, Matrix.diag, traceInput] at this ⊢
      rw [← this, Fintype.sum_prod_type]
  refine ⟨⟨hint, fun x => g67h_T_psd rho _ hrho.1 (hPpsd x), _, hsig, hInt⟩, hInt, ?_⟩
  intro R _ x
  exact g67h_trace_id R rho (P x)
