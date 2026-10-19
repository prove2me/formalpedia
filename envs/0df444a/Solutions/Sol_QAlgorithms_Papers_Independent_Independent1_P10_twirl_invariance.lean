-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P10.twirl_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:41:07.436625+00:00
-- url     : https://prove2.me/submissions/84b63c96-20ba-48f5-8504-2a3379460c61

import Theorems.Thm_OCB2012_exists_kraus_of_cj_posSemidef
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
open QAlgorithms MeasureTheory TopologicalSpace

private abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
private abbrev UG (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

private lemma haar_prob (d : ℕ) : IsProbabilityMeasure (Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩
attribute [local instance] haar_prob

private lemma haar_left (d : ℕ) : (Schur.unitaryHaar d).IsMulLeftInvariant := by
  unfold Schur.unitaryHaar
  infer_instance
attribute [local instance] haar_left

private lemma haar_right (d : ℕ) : (Schur.unitaryHaar d).IsMulRightInvariant := by
  constructor
  intro g
  have hi := Measure.haarMeasure_unique ((Schur.unitaryHaar d).map (fun x => x * g))
    (⟨⟨Set.univ,isCompact_univ⟩,by simp⟩ : PositiveCompacts (UG d))
  change (Schur.unitaryHaar d).map (fun x => x * g) =
    ((Schur.unitaryHaar d).map (fun x => x * g)) Set.univ • Schur.unitaryHaar d at hi
  rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, one_smul] at hi
  exact hi
attribute [local instance] haar_right

private lemma haar_integrable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : UG d → F) (hf : Continuous f) : Integrable f (Schur.unitaryHaar d) := by
  simpa [IntegrableOn] using hf.continuousOn.integrableOn_of_subset_isCompact
    isCompact_univ MeasurableSet.univ Set.Subset.rfl (by simp)

private def conjL {d : ℕ} (A : Mat d) : Mat d →ₗ[ℂ] Mat d where
  toFun := conjSuperop A
  map_add' X Y := by simp [conjSuperop, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [conjSuperop]

private def krausL {d m : ℕ} (K : Fin m → Mat d) : Mat d →ₗ[ℂ] Mat d where
  toFun := krausApply K
  map_add' X Y := by simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by simp [krausApply, Finset.smul_sum]

private def rotated {d m : ℕ} (K : Fin m → Mat d) (U : UG d) (a : Fin m) : Mat d :=
  star (U : Mat d) * K a * (U : Mat d)

private lemma rotated_apply {d m : ℕ} (K : Fin m → Mat d) (U : UG d) (X : Mat d) :
    conjSuperop (star (U : Mat d)) (krausApply K (conjSuperop (U : Mat d) X)) =
      krausApply (rotated K U) X := by
  simp only [conjSuperop, krausApply, Matrix.mul_sum, Matrix.sum_mul,
    rotated, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

private lemma rotated_normalized {d m : ℕ} (K : Fin m → Mat d) (hK : IsKrausFamily K)
    (U : UG d) : IsKrausFamily (rotated K U) := by
  have hu : (U : Mat d) * (U : Mat d)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
  have hu' : (U : Mat d)ᴴ * (U : Mat d) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  change (∑ a, (rotated K U a)ᴴ * rotated K U a) = 1
  simp only [rotated, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hh (a : Fin m) :
      (U : Mat d)ᴴ * (K a)ᴴ * (U : Mat d) * (U : Mat d)ᴴ * K a * (U : Mat d) =
        (U : Mat d)ᴴ * ((K a)ᴴ * K a) * (U : Mat d) := by
    calc
      _ = (U : Mat d)ᴴ * (K a)ᴴ * ((U : Mat d) * (U : Mat d)ᴴ) * K a * (U : Mat d) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc]
  simp_rw [hh]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hK, Matrix.mul_one, hu']

private lemma integral_linear {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : Mat d →ₗ[ℂ] F) (f : UG d → Mat d) (hf : Integrable f (Schur.unitaryHaar d)) :
    L (∫ U, f U ∂Schur.unitaryHaar d) = ∫ U, L (f U) ∂Schur.unitaryHaar d :=
  (L.toContinuousLinearMap.integral_comp_comm hf).symm

private lemma twirl_covariant {d : ℕ} (hd : 0 < d) (E : Superop (Fin d) (Fin d))
    (hE : IsChannel E) (X : Mat d) (V : UG d) :
    conjSuperop (V : Mat d) (QuditFidelity.haarTwirl d hd E X) =
      QuditFidelity.haarTwirl d hd E (conjSuperop (V : Mat d) X) := by
  have hv : (V : Mat d)ᴴ * (V : Mat d) = 1 := Matrix.mem_unitaryGroup_iff'.mp V.property
  change conjL (V : Mat d) (∫ U, _ ∂Schur.unitaryHaar d) = _
  rw [integral_linear _ _ (QuditFidelity.haarTwirl_integrable d E hE X)]
  have hi := integral_mul_right_eq_self (μ := Schur.unitaryHaar d)
    (fun U : UG d => conjSuperop (star (U : Mat d))
      (E (conjSuperop (U : Mat d) (conjSuperop (V : Mat d) X)))) V⁻¹
  change _ = ∫ U, _ ∂Schur.unitaryHaar d
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with U
  change conjSuperop (V : Mat d) (conjSuperop (star (U : Mat d))
    (E (conjSuperop (U : Mat d) X))) =
    conjSuperop (star ((U * V⁻¹ : UG d) : Mat d))
      (E (conjSuperop ((U * V⁻¹ : UG d) : Mat d) (conjSuperop (V : Mat d) X)))
  simp only [conjSuperop, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, hv, Matrix.mul_one]

private def entryL {I : Type*} (i j : I) : Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma integral_entry {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (f : UG d → Matrix I I ℂ) (hf : Integrable f (Schur.unitaryHaar d)) (i j : I) :
    (∫ U, f U ∂Schur.unitaryHaar d) i j = ∫ U, f U i j ∂Schur.unitaryHaar d :=
  ((entryL i j).toContinuousLinearMap.integral_comp_comm hf).symm

private def traceL {I : Type*} [Fintype I] : Matrix I I ℂ →ₗ[ℂ] ℂ :=
  Matrix.traceLinearMap I ℂ ℂ

private lemma kraus_trace {d m : ℕ} (K : Fin m → Mat d) (X : Mat d) :
    (krausApply K X).trace = ((∑ a, (K a)ᴴ * K a) * X).trace := by
  simp only [krausApply, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.trace_mul_cycle]

private lemma kraus_preserves_trace {d m : ℕ} (K : Fin m → Mat d) (hK : IsKrausFamily K)
    (X : Mat d) : (krausApply K X).trace = X.trace := by
  rw [kraus_trace, hK, Matrix.one_mul]

private def twirlL {d m : ℕ} (K : Fin m → Mat d) : Mat d →ₗ[ℂ] Mat d where
  toFun X := ∫ U : UG d, krausApply (rotated K U) X ∂Schur.unitaryHaar d
  map_add' X Y := by
    simp only [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
    apply integral_add <;> apply haar_integrable <;> unfold rotated <;> fun_prop
  map_smul' c X := by
    simp only [krausApply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    exact integral_smul c _

private lemma twirlL_eq {d m : ℕ} (hd : 0 < d) (K : Fin m → Mat d) (X : Mat d) :
    twirlL K X = QuditFidelity.haarTwirl d hd (krausApply K) X := by
  simp only [twirlL, LinearMap.coe_mk, AddHom.coe_mk, QuditFidelity.haarTwirl, rotated_apply]

private lemma cj_kraus_eq {d m : ℕ} (K : Fin m → Mat d) :
    OCB2012.cjMatrix (krausL K) =
      ∑ a, Matrix.vecMulVec (fun p : Fin d × Fin d => conj (K a p.2 p.1))
        (star (fun p : Fin d × Fin d => conj (K a p.2 p.1))) := by
  classical
  ext p q
  change (krausApply K (Matrix.single q.1 p.1 1)) q.2 p.2 = _
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Complex.star_def, ite_and]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, mul_one]
  apply Finset.sum_congr rfl
  intro a _
  simp [mul_comm]

private lemma cj_kraus_pos {d m : ℕ} (K : Fin m → Mat d) :
    (OCB2012.cjMatrix (krausL K)).PosSemidef := by
  rw [cj_kraus_eq]
  exact Matrix.posSemidef_sum _ (fun a _ => Matrix.posSemidef_vecMulVec_self_star _)

private lemma cj_rotated_continuous {d m : ℕ} (K : Fin m → Mat d) :
    Continuous (fun U : UG d => OCB2012.cjMatrix (krausL (rotated K U))) := by
  simp_rw [cj_kraus_eq]
  unfold Matrix.vecMulVec rotated
  fun_prop

private lemma twirl_channel {d : ℕ} (hd : 0 < d) (E : Superop (Fin d) (Fin d))
    (hE : IsChannel E) : IsChannel (QuditFidelity.haarTwirl d hd E) := by
  classical
  obtain ⟨m,K,hK,hE⟩ := hE
  have he : E = krausApply K := funext hE
  subst E
  have htr (X : Mat d) : (twirlL K X).trace = X.trace := by
    change traceL (∫ U : UG d, krausApply (rotated K U) X ∂Schur.unitaryHaar d) = _
    rw [integral_linear _ _ (haar_integrable _ (by unfold krausApply rotated; fun_prop))]
    simp only [traceL, Matrix.traceLinearMap_apply, kraus_preserves_trace _ (rotated_normalized K hK _)]
    simp
  have hcj : OCB2012.cjMatrix (twirlL K) =
      ∫ U : UG d, OCB2012.cjMatrix (krausL (rotated K U)) ∂Schur.unitaryHaar d := by
    ext p q
    rw [integral_entry (fun U : UG d => OCB2012.cjMatrix (krausL (rotated K U)))
      (haar_integrable _ (cj_rotated_continuous K))]
    change (∫ U : UG d, krausApply (rotated K U) (Matrix.single q.1 p.1 1)
      ∂Schur.unitaryHaar d) q.2 p.2 = _
    exact integral_entry _ (haar_integrable _ (by unfold krausApply rotated; fun_prop)) _ _
  have hp : (OCB2012.cjMatrix (twirlL K)).PosSemidef := by
    rw [hcj]
    open scoped MatrixOrder in
      apply Matrix.nonneg_iff_posSemidef.mp
      exact integral_nonneg (fun U => (cj_kraus_pos (rotated K U)).nonneg)
  obtain ⟨A,hA⟩ := OCB2012.exists_kraus_of_cj_posSemidef (twirlL K) hp
  let B : Fin (d*d) → Mat d := fun a => A (finProdFinEquiv.symm a)
  have hB (X : Mat d) : twirlL K X = krausApply B X := by
    rw [hA]
    exact (Equiv.sum_comp finProdFinEquiv.symm (fun a => A a * X * (A a)ᴴ)).symm
  refine ⟨d*d, B, ?_, ?_⟩
  · unfold IsKrausFamily
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    rw [← kraus_trace, ← hB, htr, Matrix.one_mul]
  · intro X
    rw [← twirlL_eq hd, hB]

private def overlapL {I : Type*} [Fintype I] (P : Matrix I I ℂ) : Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun X := (P * X).trace
  map_add' X Y := by simp [Matrix.mul_add]
  map_smul' c X := by simp

private lemma overlap_integral {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (f : UG d → Matrix I I ℂ)
    (hf : Integrable f (Schur.unitaryHaar d)) :
    effectProb P (∫ U, f U ∂Schur.unitaryHaar d) =
      ∫ U, effectProb P (f U) ∂Schur.unitaryHaar d := by
  have hi := (overlapL P).toContinuousLinearMap.integral_comp_comm hf
  have hint : Integrable (fun U => (P * f U).trace) (Schur.unitaryHaar d) :=
    (overlapL P).toContinuousLinearMap.integrable_comp hf
  exact (congrArg Complex.re hi).symm.trans (integral_re hint).symm

private lemma pure_act {d : ℕ} (A : Mat d) (v : EuclideanSpace ℂ (Fin d)) :
    pureDensity (act A v) = conjSuperop A (pureDensity v) := by
  change Matrix.vecMulVec (A *ᵥ WithLp.ofLp v) (star (A *ᵥ WithLp.ofLp v)) =
    A * Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)) * Aᴴ
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

private def prepared {d : ℕ} (hd : 0 < d) (U : UG d) : Mat d :=
  pureDensity (act (U : Mat d) (ket ⟨0,hd⟩))

private lemma prepared_mul {d : ℕ} (hd : 0 < d) (U V : UG d) :
    prepared hd (U * V) = conjSuperop (U : Mat d) (prepared hd V) := by
  rw [prepared, prepared, ← pure_act (U : Mat d)]
  congr 1
  apply WithLp.ofLp_injective
  exact (Matrix.mulVec_mulVec (WithLp.ofLp (ket ⟨0,hd⟩)) (U : Mat d) (V : Mat d)).symm

private lemma overlap_rotate {d : ℕ} (P X : Mat d) (U : UG d) :
    effectProb P (conjSuperop (star (U : Mat d)) X) =
      effectProb (conjSuperop (U : Mat d) P) X := by
  unfold effectProb conjSuperop
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  congr 1
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private lemma average_unitary {d : ℕ} (hd : 0 < d) (E : Superop (Fin d) (Fin d))
    (hE : IsChannel E) :
    QuditFidelity.averageFidelity d hd E =
      ∫ U : UG d, effectProb (prepared hd U) (E (prepared hd U)) ∂Schur.unitaryHaar d := by
  change Mat d → Mat d at E
  have hcE : Continuous (E : Mat d → Mat d) := QuditFidelity.channel_continuous E hE
  have hc : Continuous (fun v : EuclideanSpace ℂ (Fin d) => effectProb (pureDensity v) (E (pureDensity v))) := by
    unfold effectProb pureDensity
    fun_prop
  unfold QuditFidelity.averageFidelity QuditFidelity.haarPureStateLaw
  exact integral_map (QuditFidelity.haarState_continuous d hd).measurable.aemeasurable
    hc.aestronglyMeasurable

private lemma twirl_average {d : ℕ} (hd : 0 < d) (E : Superop (Fin d) (Fin d))
    (hE : IsChannel E) :
    QuditFidelity.averageFidelity d hd (QuditFidelity.haarTwirl d hd E) =
      QuditFidelity.averageFidelity d hd E := by
  rw [average_unitary hd _ (twirl_channel hd E hE), average_unitary hd E hE]
  have hpoint (V : UG d) :
      effectProb (prepared hd V) (QuditFidelity.haarTwirl d hd E (prepared hd V)) =
        ∫ U : UG d, effectProb (prepared hd (U*V)) (E (prepared hd (U*V))) ∂Schur.unitaryHaar d := by
    unfold QuditFidelity.haarTwirl
    rw [overlap_integral _ _ (QuditFidelity.haarTwirl_integrable d E hE _)]
    apply integral_congr_ae
    filter_upwards [] with U
    rw [overlap_rotate, prepared_mul]
  simp_rw [hpoint]
  change Mat d → Mat d at E
  have hcE : Continuous (E : Mat d → Mat d) := QuditFidelity.channel_continuous E hE
  have hc : Continuous (fun p : UG d × UG d =>
      effectProb (prepared hd (p.2*p.1)) (E (prepared hd (p.2*p.1)))) := by
    unfold prepared pureDensity act effectProb
    fun_prop
  have hint : Integrable (fun p : UG d × UG d =>
      effectProb (prepared hd (p.2*p.1)) (E (prepared hd (p.2*p.1))))
      ((Schur.unitaryHaar d).prod (Schur.unitaryHaar d)) := by
    simpa [IntegrableOn] using hc.continuousOn.integrableOn_of_subset_isCompact
      isCompact_univ MeasurableSet.univ Set.Subset.rfl (by simp)
  rw [integral_integral_swap hint]
  simp_rw [integral_mul_left_eq_self (μ := Schur.unitaryHaar d)
    (fun U : UG d => effectProb (prepared hd U) (E (prepared hd U)))]
  simp

private lemma entanglement_kraus (d : ℕ) (hd : 0 < d) (m : ℕ)
    (K : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    QuditFidelity.entanglementFidelity d hd (krausApply K) =
      (∑ a, Complex.normSq (K a).trace) / (d : ℝ)^2 := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let P := pureDensity (finiteMaxEntangled (Fin d))
  have hs : (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : ℂ)^2 = (d : ℂ)⁻¹ := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hP (a b : Fin d × Fin d) :
      P a b = if a.1 = a.2 ∧ b.1 = b.2 then (d : ℂ)⁻¹ else 0 := by
    dsimp [P, pureDensity, finiteMaxEntangled]
    simp only [Fintype.card_fin, apply_ite, map_zero]
    split_ifs <;> simp_all [← pow_two]
  have hT (a i b j : Fin d) :
      idTensorSuperop (R := Fin d) (krausApply K) P (a,i) (b,j) =
        ∑ k, (d : ℂ)⁻¹ * K k i a * conj (K k j b) := by
    simp only [idTensorSuperop, Matrix.of_apply, krausApply, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, hP, ite_and]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq]
    apply Finset.sum_congr rfl
    intro k _
    simp [mul_comm, Finset.mem_univ]
  have htr : (P * idTensorSuperop (R := Fin d) (krausApply K) P).trace =
      (d : ℂ)⁻¹ ^ 2 * ∑ k, (K k).trace * conj (K k).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      hP, hT, ite_and]
    simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
    simp only [mul_assoc]
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  change effectProb P (idTensorSuperop (R := Fin d) (krausApply K) P) = _
  rw [effectProb, htr]
  simp only [Complex.mul_conj, ← Complex.ofReal_sum]
  have hr : (d : ℂ)⁻¹ ^ 2 = (((d : ℝ)⁻¹ ^ 2 : ℝ) : ℂ) := by simp
  rw [hr, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp [div_eq_mul_inv, inv_pow, mul_comm]

private lemma twirl_entanglement {d : ℕ} (hd : 0 < d) (E : Superop (Fin d) (Fin d))
    (hE : IsChannel E) :
    QuditFidelity.entanglementFidelity d hd (QuditFidelity.haarTwirl d hd E) =
      QuditFidelity.entanglementFidelity d hd E := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let P := pureDensity (finiteMaxEntangled (Fin d))
  let F (U : UG d) : Superop (Fin d) (Fin d) :=
    fun X => conjSuperop (star (U : Mat d)) (E (conjSuperop (U : Mat d) X))
  change Mat d → Mat d at E
  have hcE : Continuous (E : Mat d → Mat d) := QuditFidelity.channel_continuous E hE
  have hc : Continuous (fun U : UG d => idTensorSuperop (R := Fin d) (F U) P) := by
    apply continuous_pi; intro p
    apply continuous_pi; intro q
    change Continuous (fun U : UG d =>
      conjSuperop (star (U : Mat d)) (E (conjSuperop (U : Mat d)
        (Matrix.of fun i j => P (p.1,i) (q.1,j)))) p.2 q.2)
    unfold conjSuperop
    fun_prop
  have hamp : idTensorSuperop (R := Fin d) (QuditFidelity.haarTwirl d hd E) P =
      ∫ U : UG d, idTensorSuperop (R := Fin d) (F U) P ∂Schur.unitaryHaar d := by
    ext p q
    rw [integral_entry _ (haar_integrable _ hc)]
    change (∫ U : UG d, conjSuperop (star (U : Mat d))
      (E (conjSuperop (U : Mat d) (Matrix.of fun i j => P (p.1,i) (q.1,j))))
        ∂Schur.unitaryHaar d) p.2 q.2 = _
    exact integral_entry _ (QuditFidelity.haarTwirl_integrable d E hE _) _ _
  have hpoint (U : UG d) : QuditFidelity.entanglementFidelity d hd (F U) =
      QuditFidelity.entanglementFidelity d hd E := by
    obtain ⟨m,K,_,hK⟩ := hE
    have he : E = krausApply K := funext hK
    have hF : F U = krausApply (rotated K U) := by
      funext X
      change conjSuperop (star (U : Mat d)) (E (conjSuperop (U : Mat d) X)) = _
      rw [he, rotated_apply]
    rw [hF, he, entanglement_kraus, entanglement_kraus]
    congr 2
    funext a
    congr 1
    unfold rotated
    rw [Matrix.trace_mul_cycle]
    have hu : (U : Mat d) * (U : Mat d)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
    simp only [Matrix.star_eq_conjTranspose, hu, Matrix.one_mul]
  change effectProb P (idTensorSuperop (R := Fin d) (QuditFidelity.haarTwirl d hd E) P) = _
  rw [hamp, overlap_integral P _ (haar_integrable _ hc)]
  change (∫ U : UG d, QuditFidelity.entanglementFidelity d hd (F U) ∂Schur.unitaryHaar d) = _
  simp_rw [hpoint]
  simp

/-- Nielsen, Eqs. (6), (8), and (10), including the finite Kraus channel property. -/
theorem solution (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    IsChannel (QuditFidelity.haarTwirl d hd E) ∧
    QuditFidelity.averageFidelity d hd (QuditFidelity.haarTwirl d hd E) =
      QuditFidelity.averageFidelity d hd E ∧
    QuditFidelity.entanglementFidelity d hd (QuditFidelity.haarTwirl d hd E) =
      QuditFidelity.entanglementFidelity d hd E ∧
    ∀ (rho : Matrix (Fin d) (Fin d) ℂ), IsDensityMatrix rho →
      ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
        conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) (QuditFidelity.haarTwirl d hd E rho) =
          QuditFidelity.haarTwirl d hd E (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) rho) := by
  exact ⟨twirl_channel hd E hE, twirl_average hd E hE, twirl_entanglement hd E hE,
    fun rho _ V => twirl_covariant hd E hE rho V⟩
