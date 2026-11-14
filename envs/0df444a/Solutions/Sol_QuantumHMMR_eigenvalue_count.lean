-- Prove2me | solution 1 for QuantumHMMR.eigenvalue_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T21:18:52.174214+00:00
-- url     : https://prove2.me/submissions/cec66c1d-9fb6-429d-b763-e3a3df73abe0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Matrix.Normed
import Definitions.Def_QuantumHMMR_IsAcceptanceMatrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_QuantumHMMR_stepLaw
import Definitions.Def_QuantumHMMR_walkLaw
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_QuantumHMMR_lemma_4_2


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open QAlgorithms QuantumHMMR
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

namespace PRUAcceptance

/-- Separating selected wires from untouched wires is a bijective change of basis. -/
noncomputable def wireSplit {k n : ℕ} (w : Fin k ↪ Fin n) :
    Qubits n ≃ (Qubits k × ({a : Fin n // a ∉ Set.range w} → Bool)) := by
  classical
  refine { toFun := fun y => (y ∘ w, fun a => y a)
           invFun := fun p a => if h : a ∈ Set.range w then p.1 h.choose else p.2 ⟨a,h⟩
           left_inv := ?_, right_inv := ?_ }
  · intro y
    funext a
    dsimp only
    split_ifs with h
    · exact congrArg y h.choose_spec
    · rfl
  · intro p
    apply Prod.ext
    · funext b
      dsimp only [Function.comp_def]
      rw [dif_pos (Set.mem_range_self b)]
      exact congrArg p.1 (w.injective (Exists.choose_spec (Set.mem_range_self b)))
    · funext a
      exact dif_neg a.property

lemma embed_eq_kronecker {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin n) :
    embedOp M w = (Matrix.kronecker M
      (1 : Matrix ({a : Fin n // a ∉ Set.range w} → Bool)
        ({a : Fin n // a ∉ Set.range w} → Bool) ℂ)).submatrix (wireSplit w) (wireSplit w) := by
  classical
  ext y z
  have heq : (∀ a : Fin n, a ∉ Set.range w → y a = z a) ↔
      (fun a : {a : Fin n // a ∉ Set.range w} => y a) = (fun a : {a : Fin n // a ∉ Set.range w} => z a) := by
    constructor
    · intro h; funext a; exact h a a.property
    · intro h a ha; exact congrFun h ⟨a,ha⟩
  change (if ∀ a : Fin n, a ∉ Set.range w → y a = z a then M (y ∘ w) (z ∘ w) else 0) =
    M (y ∘ w) (z ∘ w) * (if (fun a : {a : Fin n // a ∉ Set.range w} => y a) =
      (fun a : {a : Fin n // a ∉ Set.range w} => z a) then 1 else 0)
  simp only [heq, mul_ite, mul_one, mul_zero]

lemma unitary_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (M : Matrix ι ι ℂ)
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) (e : κ ≃ ι) :
    M.submatrix e e ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  simpa! [Matrix.star_eq_conjTranspose] using congrArg (fun X : Matrix ι ι ℂ => X.submatrix e e) hM.1

theorem embed_unitary {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  classical
  rw [embed_eq_kronecker]
  apply unitary_submatrix
  exact Matrix.kronecker_mem_unitary hM (Submonoid.one_mem _)

lemma orderedProd_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    (U : Fin t → Matrix ι ι ℂ) (hU : ∀ i, U i ∈ Matrix.unitaryGroup ι ℂ) :
    orderedProd U ∈ Matrix.unitaryGroup ι ℂ := by
  apply Submonoid.list_prod_mem
  intro M hM
  simp only [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨i,rfl⟩ := hM
  exact hU i

theorem adaptiveState_isState {n t : ℕ} (alg : AdaptiveAlg n t)
    (U : QAlgorithms.Papers.Independent.Extend50.P45.QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) : IsState (adaptiveState alg U) := by
  unfold adaptiveState IsState
  rw [act_norm_of_mem_unitaryGroup]
  · simp [zeroKet, ket]
  · apply Submonoid.mul_mem
    · exact (alg.A (Fin.last t)).property
    · apply orderedProd_unitary
      intro i
      exact Submonoid.mul_mem _ (embed_unitary U hU _) (alg.A i.castSucc).property

/-- The Born probability is the quadratic form of the effect. -/
lemma pure_effectProb {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    effectProb M (pureDensity ψ) = (star (WithLp.ofLp ψ) ⬝ᵥ (M *ᵥ WithLp.ofLp ψ)).re := by
  unfold effectProb
  congr 1
  simp only [pureDensity, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem effectProb_mem_unitInterval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : IsEffect M) (ψ : EuclideanSpace ℂ ι) (hψ : IsState ψ) :
    0 ≤ effectProb M (pureDensity ψ) ∧ effectProb M (pureDensity ψ) ≤ 1 := by
  rw [pure_effectProb]
  have hlo := hM.1.dotProduct_mulVec_nonneg (WithLp.ofLp ψ)
  have hhi := hM.2.dotProduct_mulVec_nonneg (WithLp.ofLp ψ)
  have hn : (star (WithLp.ofLp ψ) ⬝ᵥ WithLp.ofLp ψ).re = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
    simp [show ‖ψ‖ = 1 from hψ]
  constructor
  · exact (Complex.nonneg_iff.mp hlo).1
  · have hhi' := (Complex.nonneg_iff.mp hhi).1
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re, hn] at hhi'
    linarith

theorem acceptProb_mem_unitInterval {n t : ℕ} (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) (hM : IsEffect M)
    (U : QAlgorithms.Papers.Independent.Extend50.P45.QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    0 ≤ acceptProb alg M U ∧ acceptProb alg M U ≤ 1 :=
  effectProb_mem_unitInterval M hM _ (adaptiveState_isState alg U hU)

open MeasureTheory QAlgorithms.Papers.Independent.Extend50.P45
attribute [local instance] qubitMatrixMeasurable

theorem expected_acceptance_mem_unitInterval {n t : ℕ} (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) (hM : IsEffect M)
    (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    0 ≤ ∫ U, acceptProb alg M U ∂μ ∧ (∫ U, acceptProb alg M U ∂μ) ≤ 1 := by
  have hlo : ∀ᵐ U ∂μ, 0 ≤ acceptProb alg M U :=
    hμ.mono fun U hU => (acceptProb_mem_unitInterval alg M hM U hU).1
  have hhi : ∀ᵐ U ∂μ, acceptProb alg M U ≤ 1 :=
    hμ.mono fun U hU => (acceptProb_mem_unitInterval alg M hM U hU).2
  refine ⟨integral_nonneg_of_ae hlo, ?_⟩
  simpa using integral_mono_of_nonneg hlo (integrable_const (1 : ℝ)) hhi

theorem acceptance_difference_le_one {n t : ℕ} (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) (hM : IsEffect M)
    (μ ν : Measure (QMat n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hν : ∀ᵐ U ∂ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    |(∫ U, acceptProb alg M U ∂μ) - ∫ U, acceptProb alg M U ∂ν| ≤ 1 := by
  have h1 := expected_acceptance_mem_unitInterval alg M hM μ hμ
  have h2 := expected_acceptance_mem_unitInterval alg M hM ν hν
  rw [abs_le]
  constructor <;> linarith

end PRUAcceptance



set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators Matrix.Norms.Elementwise

namespace PRUMoments

attribute [local instance] qubitMatrixMeasurable qubitMatrixBorel

def rep {n : ℕ} (t : ℕ) (U : QMat n) :
    Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
      ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ :=
  Matrix.kronecker (qubitTensorPower t U) ((qubitTensorPower t U).map (starRingEnd ℂ))

lemma rep_apply {n : ℕ} (t : ℕ) (U : QMat n) (x y) :
    rep t U x y = qubitTensorPower t U x.1 y.1 * conj (qubitTensorPower t U x.2 y.2) := rfl

lemma tensor_mul {n : ℕ} (t : ℕ) (U V : QMat n) :
    qubitTensorPower t (U * V) = qubitTensorPower t U * qubitTensorPower t V := by
  ext x y
  simp only [qubitTensorPower, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

lemma rep_mul {n : ℕ} (t : ℕ) (U V : QMat n) : rep t (U * V) = rep t U * rep t V := by
  simp only [rep, tensor_mul, Matrix.map_mul]
  exact Matrix.mul_kronecker_mul _ _ _ _

lemma tensor_one {n : ℕ} (t : ℕ) : qubitTensorPower t (1 : QMat n) = 1 := by
  ext x y
  classical
  by_cases h : x = y
  · subst y; simp [qubitTensorPower]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [qubitTensorPower, Matrix.one_apply, if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma rep_one {n : ℕ} (t : ℕ) : rep t (1 : QMat n) = 1 := by
  simp [rep, tensor_one]

lemma continuous_rep_entry {n : ℕ} (t : ℕ) (x y) : Continuous (fun U : QMat n => rep t U x y) := by
  simp only [rep_apply, qubitTensorPower]
  fun_prop

lemma unitary_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (x y : ι) : ‖U x y‖ ≤ 1 :=
  entry_norm_bound_of_unitary hU x y

lemma tensor_entry_bound {n : ℕ} (t : ℕ) (U : QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (x y) : ‖qubitTensorPower t U x y‖ ≤ 1 := by
  simp only [qubitTensorPower, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => unitary_entry_bound U hU _ _)

lemma rep_entry_bound {n : ℕ} (t : ℕ) (U : QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (x y) : ‖rep t U x y‖ ≤ 1 := by
  rw [rep_apply, norm_mul, Complex.norm_conj]
  exact mul_le_one₀ (tensor_entry_bound t U hU _ _) (norm_nonneg _) (tensor_entry_bound t U hU _ _)

lemma rep_integrable {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (x y) :
    Integrable (fun U => rep t U x y) μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_rep_entry t x y).aestronglyMeasurable
  exact hμ.mono fun U hU => rep_entry_bound t U hU x y

theorem moment_convolve {n : ℕ} (t : ℕ) (μ ν : Measure (QMat n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hν : ∀ᵐ U ∂ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    balancedUnitaryMoment (convolve μ ν) t = balancedUnitaryMoment μ t * balancedUnitaryMoment ν t := by
  ext x y
  change (∫ U, rep t U x y ∂Measure.map (fun p : QMat n × QMat n => p.1 * p.2) (μ.prod ν)) = _
  rw [integral_map (by fun_prop) (continuous_rep_entry t x y).aestronglyMeasurable]
  simp_rw [rep_mul, Matrix.mul_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_prod_mul (fun U : QMat n => rep t U x i) (fun V : QMat n => rep t V i y)
  · intro i _
    exact (rep_integrable t μ hμ x i).mul_prod (rep_integrable t ν hν i y)

lemma unitary_measurableSet (n : ℕ) : MeasurableSet
    {U : QMat n | U ∈ Matrix.unitaryGroup (Qubits n) ℂ} :=
  (isClosed_unitary : IsClosed (Matrix.unitaryGroup (Qubits n) ℂ : Set (QMat n))).measurableSet

lemma convolve_probability {n : ℕ} (μ ν : Measure (QMat n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (convolve μ ν) := by
  apply Measure.isProbabilityMeasure_map
  fun_prop

lemma convolve_unitary {n : ℕ} (μ ν : Measure (QMat n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hν : ∀ᵐ U ∂ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ∀ᵐ U ∂convolve μ ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold convolve
  apply (ae_map_iff (by fun_prop) (unitary_measurableSet n)).2
  apply (Measure.ae_prod_iff_ae_ae ((unitary_measurableSet n).preimage (by fun_prop))).2
  exact hμ.mono fun U hU => hν.mono fun V hV => Submonoid.mul_mem _ hU hV

lemma steps_probability {n : ℕ} (μ : Measure (QMat n)) [IsProbabilityMeasure μ] (r : ℕ) :
    IsProbabilityMeasure (steps μ r) := by
  induction r with
  | zero => simp only [steps]; infer_instance
  | succ r ih => letI := ih; exact convolve_probability μ (steps μ r)

lemma steps_unitary {n : ℕ} (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (r : ℕ) :
    ∀ᵐ U ∂steps μ r, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  induction r with
  | zero =>
    exact (ae_dirac_iff (unitary_measurableSet n)).2 (Submonoid.one_mem (Matrix.unitaryGroup (Qubits n) ℂ))
  | succ r ih =>
    letI := steps_probability μ r
    exact convolve_unitary μ (steps μ r) hμ ih

theorem moment_steps {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (r : ℕ) :
    balancedUnitaryMoment (steps μ r) t = balancedUnitaryMoment μ t ^ r := by
  induction r with
  | zero =>
    ext x y
    change (∫ U, rep t U x y ∂Measure.dirac (1 : QMat n)) = _
    simp [rep_one]
  | succ r ih =>
    letI := steps_probability μ r
    rw [steps, moment_convolve t μ (steps μ r) hμ (steps_unitary μ hμ r), ih, pow_succ']

lemma haarMap_continuous (n : ℕ) :
    Continuous (fun U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ =>
      (fun x y => U.val (bitsEquivFin n x) (bitsEquivFin n y) : QMat n)) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)

lemma haar_probability (n : ℕ) : IsProbabilityMeasure (haarLaw n) := by
  letI : IsProbabilityMeasure (Schur.unitaryHaar (2 ^ n)) := ⟨Measure.haarMeasure_self⟩
  exact Measure.isProbabilityMeasure_map (Continuous.measurable (γ := QMat n) (haarMap_continuous n)).aemeasurable

lemma haar_unitary (n : ℕ) : ∀ᵐ U ∂haarLaw n, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold haarLaw
  apply (ae_map_iff (Continuous.measurable (γ := QMat n) (haarMap_continuous n)).aemeasurable (unitary_measurableSet n)).2
  exact Filter.Eventually.of_forall fun U =>
    PRUAcceptance.unitary_submatrix U.val U.property (bitsEquivFin n)

end PRUMoments



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators Matrix.Norms.Elementwise

namespace PRUHaar

attribute [local instance] qubitMatrixMeasurable qubitMatrixBorel

lemma finite_haar_rightInvariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsHaarMeasure μ] :
    Measure.IsMulRightInvariant μ := by
  constructor
  intro g
  let ν := Measure.map (fun x : G => x * g) μ
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : Measure.IsMulLeftInvariant ν := inferInstance
  letI : Measure.IsHaarMeasure ν :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior ν Set.univ isCompact_univ
      (by simp) (by simp) (by simp)
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν μ

lemma finite_haar_invInvariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsHaarMeasure μ] :
    Measure.IsInvInvariant μ := by
  letI := finite_haar_rightInvariant μ
  letI : IsProbabilityMeasure μ.inv := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : Measure.IsHaarMeasure μ.inv :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior μ.inv Set.univ isCompact_univ
      (by simp) (by simp) (by simp)
  exact ⟨Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ.inv μ⟩

def haarMap (n : ℕ) (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : QMat n :=
  U.val.submatrix (bitsEquivFin n) (bitsEquivFin n)

lemma haarMap_mul (n : ℕ) (U V : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    haarMap n (U * V) = haarMap n U * haarMap n V := by
  change ((U.val * V.val).submatrix (bitsEquivFin n) (bitsEquivFin n)) = _
  exact (Matrix.submatrix_mul_equiv U.val V.val (bitsEquivFin n) (bitsEquivFin n) (bitsEquivFin n)).symm

lemma haarMap_inv (n : ℕ) (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    haarMap n U⁻¹ = (haarMap n U)ᴴ := by
  rw [← Unitary.star_eq_inv]
  rfl

lemma rep_adjoint {n : ℕ} (t : ℕ) (U : QMat n) : PRUMoments.rep t Uᴴ = (PRUMoments.rep t U)ᴴ := by
  ext x y
  simp only [PRUMoments.rep_apply, qubitTensorPower, Matrix.conjTranspose_apply,
    map_prod, map_mul, Pi.star_apply, Complex.star_def, starRingEnd_self_apply]

lemma haar_entry (n t : ℕ) (x y) : balancedUnitaryMoment (haarLaw n) t x y =
    ∫ U, PRUMoments.rep t (haarMap n U) x y ∂Schur.unitaryHaar (2 ^ n) := by
  change (∫ U, PRUMoments.rep t U x y ∂haarLaw n) = _
  unfold haarLaw
  rw [integral_map (Continuous.measurable (γ := QMat n) (PRUMoments.haarMap_continuous n)).aemeasurable
    (PRUMoments.continuous_rep_entry t x y).aestronglyMeasurable]
  rfl

theorem haar_isHermitian (n t : ℕ) : (balancedUnitaryMoment (haarLaw n) t).IsHermitian := by
  letI : IsProbabilityMeasure (Schur.unitaryHaar (2 ^ n)) := ⟨Measure.haarMeasure_self⟩
  letI : Measure.IsHaarMeasure (Schur.unitaryHaar (2 ^ n)) := by
    unfold Schur.unitaryHaar
    infer_instance
  letI := finite_haar_invInvariant (Schur.unitaryHaar (2 ^ n))
  ext x y
  rw [Matrix.conjTranspose_apply, haar_entry, haar_entry, Complex.star_def, ← integral_conj]
  have h (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
      conj (PRUMoments.rep t (haarMap n U) y x) = PRUMoments.rep t (haarMap n U⁻¹) x y := by
    rw [haarMap_inv, rep_adjoint]
    rfl
  simp_rw [h]
  exact integral_inv_eq_self (fun U => PRUMoments.rep t (haarMap n U) x y) (Schur.unitaryHaar (2 ^ n))

lemma haar_rep_integrable (n t : ℕ) (x y) :
    Integrable (fun U => PRUMoments.rep t (haarMap n U) x y) (Schur.unitaryHaar (2 ^ n)) := by
  letI : IsProbabilityMeasure (Schur.unitaryHaar (2 ^ n)) := ⟨Measure.haarMeasure_self⟩
  apply (integrable_const (1 : ℝ)).mono'
    ((PRUMoments.continuous_rep_entry t x y).comp (PRUMoments.haarMap_continuous n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun U => PRUMoments.rep_entry_bound t _
    (PRUAcceptance.unitary_submatrix U.val U.property (bitsEquivFin n)) x y

lemma haar_left_group (n t : ℕ) (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    PRUMoments.rep t (haarMap n U) * balancedUnitaryMoment (haarLaw n) t =
      balancedUnitaryMoment (haarLaw n) t := by
  letI : Measure.IsHaarMeasure (Schur.unitaryHaar (2 ^ n)) := by
    unfold Schur.unitaryHaar
    infer_instance
  ext x y
  simp only [Matrix.mul_apply, haar_entry]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun i _ => (haar_rep_integrable n t i y).const_mul _)]
  have h (V : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
      ∑ i, PRUMoments.rep t (haarMap n U) x i * PRUMoments.rep t (haarMap n V) i y =
        PRUMoments.rep t (haarMap n (U * V)) x y := by
    rw [haarMap_mul, PRUMoments.rep_mul, Matrix.mul_apply]
  simp_rw [h]
  exact integral_mul_left_eq_self (fun V => PRUMoments.rep t (haarMap n V) x y) U

lemma haarMap_surjective (n : ℕ) (U : QMat n) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ∃ V : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ, haarMap n V = U := by
  refine ⟨⟨U.submatrix (bitsEquivFin n).symm (bitsEquivFin n).symm,
    PRUAcceptance.unitary_submatrix U hU (bitsEquivFin n).symm⟩, ?_⟩
  ext x y
  simp [haarMap, Matrix.submatrix]

lemma haar_left {n : ℕ} (t : ℕ) (U : QMat n) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    PRUMoments.rep t U * balancedUnitaryMoment (haarLaw n) t = balancedUnitaryMoment (haarLaw n) t := by
  obtain ⟨V,rfl⟩ := haarMap_surjective n U hU
  exact haar_left_group n t V

lemma haar_right {n : ℕ} (t : ℕ) (U : QMat n) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    balancedUnitaryMoment (haarLaw n) t * PRUMoments.rep t U = balancedUnitaryMoment (haarLaw n) t := by
  have h := congrArg Matrix.conjTranspose (haar_left t Uᴴ (Unitary.star_mem hU))
  simpa only [Matrix.conjTranspose_mul, rep_adjoint, Matrix.conjTranspose_conjTranspose,
    (haar_isHermitian n t).eq] using h

lemma haar_idempotent (n t : ℕ) :
    balancedUnitaryMoment (haarLaw n) t * balancedUnitaryMoment (haarLaw n) t =
      balancedUnitaryMoment (haarLaw n) t := by
  letI : IsProbabilityMeasure (Schur.unitaryHaar (2 ^ n)) := ⟨Measure.haarMeasure_self⟩
  ext x y
  rw [Matrix.mul_apply]
  conv_lhs => arg 2; ext i; rw [haar_entry]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum Finset.univ (fun i _ => (haar_rep_integrable n t x i).mul_const _)]
  have h (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
      ∑ i, PRUMoments.rep t (haarMap n U) x i * balancedUnitaryMoment (haarLaw n) t i y =
        balancedUnitaryMoment (haarLaw n) t x y :=
    congrFun (congrFun (haar_left_group n t U) x) y
  simp_rw [h]
  simp

end PRUHaar




set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators ENNReal

namespace PRUWalkLaws

attribute [local instance] qubitMatrixMeasurable qubitMatrixBorel

lemma nextWire_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : nextWire i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  unfold nextWire at hv
  split_ifs at hv <;> simp only at hv <;> omega

def edgeWires {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : Fin 2 ↪ Fin n where
  toFun j := if j.val = 0 then i else nextWire i
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [nextWire_ne hn i, Ne.symm (nextWire_ne hn i)]


lemma edgeLift_eq_embed {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (U : QMat 2) :
    edgeLift i U = embedOp U (edgeWires hn i) := by
  ext x y
  have hrange (q : Fin n) : q ∈ Set.range (edgeWires hn i) ↔ q = i ∨ q = nextWire i := by
    simp only [Set.mem_range, Fin.exists_fin_two, edgeWires, Function.Embedding.coeFn_mk]
    simp [eq_comm]
  have houtside : (∀ q, q ≠ i → q ≠ nextWire i → x q = y q) ↔
      (∀ q, q ∉ Set.range (edgeWires hn i) → x q = y q) := by
    simp only [hrange, not_or, and_imp]
  simp only [edgeLift, embedOp, Matrix.of_apply, ← houtside]
  split_ifs
  · congr 1 <;> funext j <;> fin_cases j <;> simp [edgeWires, Function.comp_def]
  · rfl

lemma edgeLift_unitary {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (U : QMat 2)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 2) ℂ) :
    edgeLift i U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [edgeLift_eq_embed hn]
  exact PRUAcceptance.embed_unitary U hU _

lemma firstWireLift_unitary (n : ℕ) (U : QMat 1)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 1) ℂ) :
    firstWireLift n U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  by_cases hn : 0 < n
  · let w : Fin 1 ↪ Fin n := ⟨fun _ => ⟨0,hn⟩, fun _ _ _ => Subsingleton.elim _ _⟩
    have heq : firstWireLift n U = embedOp U w := by
      ext x y
      have hrange (q : Fin n) : q ∈ Set.range w ↔ q.val = 0 := by
        constructor
        · rintro ⟨j,rfl⟩; rfl
        · intro h; exact ⟨0, Fin.ext h.symm⟩
      simp only [firstWireLift, dif_pos hn, embedOp, Matrix.of_apply, hrange]
      split_ifs <;> rfl
    rw [heq]
    exact PRUAcceptance.embed_unitary U hU w
  · have heq : firstWireLift n U = 1 := by ext x y; simp [firstWireLift, hn]
    rw [heq]; exact Submonoid.one_mem _

lemma rotZ_unitary (φ : ℝ) : rotZ φ ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [rotZ, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases h : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
    split_ifs
    all_goals
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [Complex.norm_exp]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

lemma continuous_firstWireLift (n : ℕ) : Continuous (firstWireLift n) := by
  apply continuous_pi; intro x
  apply continuous_pi; intro y
  simp only [firstWireLift]
  split_ifs <;> fun_prop

lemma continuous_rotZ : Continuous rotZ := by
  apply continuous_pi; intro x
  apply continuous_pi; intro y
  simp only [rotZ, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

lemma chi_probability (G : Finset (Clifford.ProjectiveGroup 2)) (n : ℕ)
    (hG : G.Nonempty) (hn : 0 < n) : IsProbabilityMeasure (chiLaw G n) := by
  constructor
  have hg : (G.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hG.card_pos.ne'
  have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  simp [chiLaw, Measure.smul_apply, Measure.finsetSum_apply, hg, hn', ENNReal.inv_mul_cancel]

lemma chi_unitary (G : Finset (Clifford.ProjectiveGroup 2)) (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ U ∂chiLaw G n, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold chiLaw
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro g hg
  apply (ae_dirac_iff (PRUMoments.unitary_measurableSet n)).2
  exact edgeLift_unitary hn i _ (Clifford.representative g).val.property

lemma xi_probability (n : ℕ) : IsProbabilityMeasure (xiLaw n) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  letI : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by simp only [Real.volume_Ico, sub_zero, ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hp)
      (by simp only [Real.volume_Ico, sub_zero]; exact ENNReal.ofReal_ne_top)
  unfold xiLaw
  apply Measure.isProbabilityMeasure_map
  exact (Continuous.measurable (γ := QMat n)
    ((continuous_firstWireLift n).comp continuous_rotZ)).aemeasurable

lemma xi_unitary (n : ℕ) : ∀ᵐ U ∂xiLaw n, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold xiLaw
  apply (ae_map_iff (Continuous.measurable (γ := QMat n)
    ((continuous_firstWireLift n).comp continuous_rotZ)).aemeasurable
    (PRUMoments.unitary_measurableSet n)).2
  exact Filter.Eventually.of_forall fun φ => firstWireLift_unitary n _ (rotZ_unitary φ)

lemma step_probability (G : Finset (Clifford.ProjectiveGroup 2)) (n m : ℕ)
    (hG : G.Nonempty) (hn : 0 < n) (hm : 1 ≤ m) : IsProbabilityMeasure (stepLaw G n m) := by
  letI := chi_probability G n hG hn
  letI := xi_probability n
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hinv0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  have hinv1 : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm'
  constructor
  simp only [stepLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hinv1) hinv0]
  simp

lemma step_unitary (G : Finset (Clifford.ProjectiveGroup 2)) (n m : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ U ∂stepLaw G n m, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold stepLaw
  rw [ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (chi_unitary G n hn) _,
    Measure.ae_smul_measure (xi_unitary n) _⟩

theorem walk_probability (G : Finset (Clifford.ProjectiveGroup 2)) (n m r : ℕ)
    (hG : G.Nonempty) (hn : 0 < n) (hm : 1 ≤ m) : IsProbabilityMeasure (walkLaw G n m r) := by
  letI := step_probability G n m hG hn hm
  exact PRUMoments.steps_probability (stepLaw G n m) r

theorem walk_unitary (G : Finset (Clifford.ProjectiveGroup 2)) (n m r : ℕ)
    (hG : G.Nonempty) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    ∀ᵐ U ∂walkLaw G n m r, U ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  letI := step_probability G n m hG (by omega) hm
  exact PRUMoments.steps_unitary (stepLaw G n m) (step_unitary G n m hn) r

theorem walk_moment (G : Finset (Clifford.ProjectiveGroup 2)) (n m r t : ℕ)
    (hG : G.Nonempty) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    balancedUnitaryMoment (walkLaw G n m r) t = balancedUnitaryMoment (stepLaw G n m) t ^ r := by
  letI := step_probability G n m hG (by omega) hm
  exact PRUMoments.moment_steps t (stepLaw G n m) (step_unitary G n m hn) r

end PRUWalkLaws



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

namespace PRUSpectralGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normSq (v : ι → ℂ) : ℝ := (star v ⬝ᵥ v).re

lemma normSq_nonneg (v : ι → ℂ) : 0 ≤ normSq v :=
  (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).1

lemma normSq_eq_zero (v : ι → ℂ) : normSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply dotProduct_star_self_eq_zero.mp
    apply Complex.ext h
    exact (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).2.symm
  · rintro rfl; simp [normSq]

lemma ker_orthogonal (P : Matrix ι ι ℂ) (hP : P.IsHermitian)
    (v : ι → ℂ) (hv : P *ᵥ v = 0) (w : ι → ℂ) : star v ⬝ᵥ (P *ᵥ w) = 0 := by
  rw [Matrix.dotProduct_mulVec, ← hP, Matrix.vecMul_conjTranspose, star_star, hv]
  simp

lemma projection_eigenvector (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hP : P.IsHermitian) (hMP : M * P = P) (hPM : P * M = P) (hPP : P * P = P)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ v : ι → ℂ, P *ᵥ v = 0 →
      c * normSq v ≤ (star v ⬝ᵥ ((1 - M) *ᵥ v)).re)
    (i : ι) :
    P *ᵥ ⇑(hM.eigenvectorBasis i) =
      if hM.eigenvalues i = 1 then ⇑(hM.eigenvectorBasis i) else 0 := by
  classical
  let v : ι → ℂ := ⇑(hM.eigenvectorBasis i)
  have hev : M *ᵥ v = (hM.eigenvalues i : ℂ) • v := by
    simpa only [v, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hM.mulVec_eigenvectorBasis i
  by_cases hi : hM.eigenvalues i = 1
  · rw [if_pos hi]
    have hMv : M *ᵥ v = v := by simpa [hi] using hev
    let u := v - P *ᵥ v
    have hPu : P *ᵥ u = 0 := by
      simp only [u, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPP, sub_self]
    have hMu : M *ᵥ u = u := by
      simp only [u, Matrix.mulVec_sub, hMv, Matrix.mulVec_mulVec, hMP]
    have hz : normSq u = 0 := by
      have h := hgap u hPu
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, hMu, sub_self, dotProduct_zero,
        Complex.zero_re] at h
      nlinarith [normSq_nonneg u]
    have hu : u = 0 := (normSq_eq_zero u).mp hz
    exact (sub_eq_zero.mp hu).symm
  · rw [if_neg hi]
    have heq : (hM.eigenvalues i : ℂ) • (P *ᵥ v) = P *ᵥ v := by
      rw [← Matrix.mulVec_smul, ← hev, Matrix.mulVec_mulVec, hPM]
    have hn : (hM.eigenvalues i : ℂ) ≠ 1 := by exact_mod_cast hi
    have hz : ((hM.eigenvalues i : ℂ) - 1) • (P *ᵥ v) = 0 := by
      rw [sub_smul, one_smul, heq, sub_self]
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

lemma eigenvalue_upper (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hgap : ∀ v : ι → ℂ, P *ᵥ v = 0 →
      c * normSq v ≤ (star v ⬝ᵥ ((1 - M) *ᵥ v)).re)
    (i : ι) (hi : P *ᵥ ⇑(hM.eigenvectorBasis i) = 0) : hM.eigenvalues i ≤ 1 - c := by
  have hn : normSq ⇑(hM.eigenvectorBasis i) = 1 := by
    unfold normSq
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
    simp [hM.eigenvectorBasis.orthonormal.norm_eq_one]
  have h := hgap _ hi
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at h
  change c * normSq ⇑(hM.eigenvectorBasis i) ≤ normSq ⇑(hM.eigenvectorBasis i) -
    (star ⇑(hM.eigenvectorBasis i) ⬝ᵥ (M *ᵥ ⇑(hM.eigenvectorBasis i))).re at h
  have hev : hM.eigenvalues i = (star ⇑(hM.eigenvectorBasis i) ⬝ᵥ (M *ᵥ ⇑(hM.eigenvectorBasis i))).re := by
    simpa! using hM.eigenvalues_eq i
  rw [hn, ← hev] at h
  linarith

lemma projection_diagonalization (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hPv : ∀ i, P *ᵥ ⇑(hM.eigenvectorBasis i) =
      if hM.eigenvalues i = 1 then ⇑(hM.eigenvectorBasis i) else 0) :
    P = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary
      (Matrix.diagonal (fun i => if hM.eigenvalues i = 1 then (1 : ℂ) else 0)) := by
  classical
  have hPV : P * (hM.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hM.eigenvectorUnitary : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => if hM.eigenvalues i = 1 then (1 : ℂ) else 0) := by
    ext a i
    rw [Matrix.mul_diagonal]
    change (P *ᵥ ⇑(hM.eigenvectorBasis i)) a = _
    rw [hPv]
    split_ifs <;> simp [Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [Unitary.conjStarAlgAut_apply, ← hPV, Matrix.mul_assoc]
  simp

lemma segment_diagonalization (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hPv : ∀ i, P *ᵥ ⇑(hM.eigenvectorBasis i) =
      if hM.eigenvalues i = 1 then ⇑(hM.eigenvectorBasis i) else 0) (m : ℕ) :
    M ^ m - P = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary
      (Matrix.diagonal (fun i => if hM.eigenvalues i = 1 then (0 : ℂ)
        else (hM.eigenvalues i : ℂ) ^ m)) := by
  classical
  rw [projection_diagonalization M P hM hPv]
  conv_lhs => lhs; rw [hM.spectral_theorem, ← map_pow]
  rw [← map_sub]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_pow, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Pi.pow_apply, Function.comp_def]
    split_ifs with hi
    · simp [hi]
    · simp
  · simp [Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ hij, hij]

/-- Spectral multiplicities can be read from any unitary diagonalization. -/
lemma eigenvalue_multiset_of_diagonalization (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ)
    (hd : B = Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (d i : ℂ)))) :
    (Finset.univ.val.map hB.eigenvalues) = Finset.univ.val.map d := by
  have hchar : B.charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i : ℂ)) := by
    rw [hd, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.charpoly_diagonal]
  have hroots := hB.roots_charpoly_eq_eigenvalues
  rw [hchar, Polynomial.roots_prod] at hroots
  · have heq : (Finset.univ.val.map (fun i => (d i : ℂ))) =
        Finset.univ.val.map (fun i => (hB.eigenvalues i : ℂ)) := by
      simpa only [Polynomial.roots_X_sub_C, Finset.sum_singleton, Multiset.bind_singleton,
        Function.comp_def] using! hroots
    have hreal := congrArg (Multiset.map Complex.re) heq
    simpa only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] using hreal.symm
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _

lemma eigenvalue_bound_of_multiset (a d : ι → ℝ)
    (heq : Finset.univ.val.map a = Finset.univ.val.map d)
    (r : ℝ) (hd : ∀ i, |d i| ≤ r) : ∀ i, |a i| ≤ r := by
  intro i
  have hi : a i ∈ Finset.univ.val.map a := Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  rw [heq] at hi
  obtain ⟨j,hj,hij⟩ := Multiset.mem_map.mp hi
  rw [← hij]
  exact hd j

lemma eigenvalue_count_of_multiset (a d : ι → ℝ)
    (heq : Finset.univ.val.map a = Finset.univ.val.map d) (r : ℝ) :
    (Finset.univ.filter fun i => r < |a i|).card =
      (Finset.univ.filter fun i => r < |d i|).card := by
  classical
  have h := congrArg (fun s : Multiset ℝ => (s.filter fun x => r < |x|).card) heq
  simpa only [Multiset.filter_map, Multiset.card_map, Function.comp_def,
    ← Finset.filter_val, Finset.card_def] using h

/-- A gap away from a fixed projection persists under taking a whole walk segment.
The count concerns eigenvalues with multiplicity, including negative eigenvalues. -/
theorem segment_spectrum (M P : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (hP : P.IsHermitian) (hMP : M * P = P) (hPM : P * M = P) (hPP : P * P = P)
    (c θ : ℝ) (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθc : θ ≤ 1 - c)
    (hgap : ∀ v : ι → ℂ, P *ᵥ v = 0 →
      c * normSq v ≤ (star v ⬝ᵥ ((1 - M) *ᵥ v)).re)
    (hnegative : ∀ i, hM.eigenvalues i < 0 → |hM.eigenvalues i| ≤ θ)
    (D m : ℕ) (hcount : (Finset.univ.filter fun i => θ < hM.eigenvalues i).card ≤ D) :
    (M ^ m - P) * P = 0 ∧ (M ^ m - P).IsHermitian ∧
      ∀ hB : (M ^ m - P).IsHermitian,
        (∀ i, |hB.eigenvalues i| ≤ (1 - c) ^ m) ∧
        (Finset.univ.filter fun i => θ ^ m < |hB.eigenvalues i|).card ≤ D := by
  classical
  have hpow : ∀ r : ℕ, M ^ r * P = P := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, mul_assoc, hMP, ih]
  refine ⟨by rw [sub_mul, hpow, hPP, sub_self], (hM.pow m).sub hP, ?_⟩
  intro hB
  have hPv := projection_eigenvector M P hM hP hMP hPM hPP c hc hgap
  let d : ι → ℝ := fun i => if hM.eigenvalues i = 1 then 0 else hM.eigenvalues i ^ m
  have hdiag : M ^ m - P = Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary
      (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [segment_diagonalization M P hM hPv m]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, d]
      split_ifs <;> simp
    · simp [hij]
  have heq := eigenvalue_multiset_of_diagonalization _ hB hM.eigenvectorUnitary d hdiag
  have hc1 : 0 ≤ 1 - c := hθ0.trans hθc
  constructor
  · apply eigenvalue_bound_of_multiset _ d heq
    intro i
    by_cases hi : hM.eigenvalues i = 1
    · simp only [d, if_pos hi, abs_zero]
      positivity
    · have hPi : P *ᵥ ⇑(hM.eigenvectorBasis i) = 0 := by simpa only [if_neg hi] using hPv i
      have hu := eigenvalue_upper M P hM c hgap i hPi
      have habs : |hM.eigenvalues i| ≤ 1 - c := by
        by_cases hneg : hM.eigenvalues i < 0
        · exact (hnegative i hneg).trans hθc
        · rw [abs_of_nonneg (le_of_not_gt hneg)]
          exact hu
      simp only [d, if_neg hi, abs_pow]
      gcongr
  · rw [eigenvalue_count_of_multiset _ d heq]
    apply le_trans (Finset.card_le_card _) hcount
    intro i hi
    have hgt := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have hle : hM.eigenvalues i ≤ θ := le_of_not_gt hnot
    have hsmall : |d i| ≤ θ ^ m := by
      by_cases hione : hM.eigenvalues i = 1
      · simp only [d, if_pos hione, abs_zero]
        positivity
      · have habs : |hM.eigenvalues i| ≤ θ := by
          by_cases hneg : hM.eigenvalues i < 0
          · exact hnegative i hneg
          · rwa [abs_of_nonneg (le_of_not_gt hneg)]
        simp only [d, if_neg hione, abs_pow]
        gcongr
    exact (not_lt_of_ge hsmall) hgt

end PRUSpectralGap



set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ComplexConjugate BigOperators ComplexOrder

namespace PRUMinMax
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normSq_eq (v : EuclideanSpace ℂ ι) :
    PRUSpectralGap.normSq ⇑v = ‖v‖ ^ 2 := by
  simpa! only [PRUSpectralGap.normSq, EuclideanSpace.inner_eq_star_dotProduct,
    RCLike.re_to_complex, dotProduct_comm] using (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm

lemma quadratic_eq (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    (star ⇑v ⬝ᵥ (M *ᵥ ⇑v)).re = (inner ℂ v (Matrix.toEuclideanLin M v)).re := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply]
  rw [dotProduct_comm]

lemma eigenvector_map (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (i : ι) :
    Matrix.toEuclideanLin M (hM.eigenvectorBasis i) =
      (hM.eigenvalues i : ℂ) • hM.eigenvectorBasis i := by
  apply PiLp.ext
  intro j
  simpa! only [Matrix.ofLp_toEuclideanLin_apply, PiLp.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using
    congrFun (hM.mulVec_eigenvectorBasis i) j

lemma fast_combination (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (θ : ℝ)
    (f : {i : ι // θ < hM.eigenvalues i} → ℂ) :
    let v := ∑ i, f i • hM.eigenvectorBasis i.val
    (inner ℂ v (Matrix.toEuclideanLin M v)).re - θ * ‖v‖ ^ 2 =
      ∑ i, (hM.eigenvalues i.val - θ) * ‖f i‖ ^ 2 := by
  classical
  dsimp only
  have ho := hM.eigenvectorBasis.orthonormal.comp
    (fun i : {i : ι // θ < hM.eigenvalues i} => i.val) Subtype.val_injective
  have hnorm : ‖∑ i, f i • hM.eigenvectorBasis i.val‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
    have h := ho.inner_sum f f Finset.univ
    have hr := congrArg Complex.re h
    simpa! [inner_self_eq_norm_sq_to_K, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] using hr
  rw [hnorm, map_sum]
  simp_rw [map_smul, eigenvector_map, smul_smul]
  have h := ho.inner_sum f (fun i => f i * (hM.eigenvalues i.val : ℂ)) Finset.univ
  dsimp only [Function.comp_def] at h
  rw [h]
  simp only [Complex.re_sum, ← mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma count_le_rank (M P : Matrix ι ι ℂ) (hM : M.IsHermitian) (θ : ℝ)
    (hb : ∀ v, P *ᵥ v = 0 →
      (star v ⬝ᵥ (M *ᵥ v)).re ≤ θ * PRUSpectralGap.normSq v) :
    (Finset.univ.filter fun i => θ < hM.eigenvalues i).card ≤ P.rank := by
  classical
  let S := {i : ι // θ < hM.eigenvalues i}
  let L := Matrix.toEuclideanLin P
  let w (i : S) : LinearMap.range L := ⟨L (hM.eigenvectorBasis i.val), by
    exact ⟨hM.eigenvectorBasis i.val,rfl⟩⟩
  have hw : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    let v := ∑ j : S, f j • hM.eigenvectorBasis j.val
    have hv : L v = 0 := by
      have h := congrArg (fun z : LinearMap.range L => z.val) hf
      simpa only [v, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Submodule.coe_zero, w] using h
    have hPv : P *ᵥ ⇑v = 0 := by
      have h := congrArg WithLp.ofLp hv
      simpa only [L, Matrix.ofLp_toEuclideanLin_apply, WithLp.ofLp_zero] using h
    have hb' := hb ⇑v hPv
    rw [normSq_eq, quadratic_eq] at hb'
    have hc := fast_combination M hM θ f
    change (inner ℂ v (Matrix.toEuclideanLin M v)).re - θ * ‖v‖ ^ 2 = _ at hc
    have hs : ∑ j : S, (hM.eigenvalues j.val - θ) * ‖f j‖ ^ 2 ≤ 0 := by linarith
    have hi : (hM.eigenvalues i.val - θ) * ‖f i‖ ^ 2 ≤ 0 :=
      (Finset.single_le_sum (f := fun j : S => (hM.eigenvalues j.val - θ) * ‖f j‖ ^ 2) (fun j _ => mul_nonneg (sub_nonneg.mpr j.property.le) (sq_nonneg _))
        (Finset.mem_univ i)).trans hs
    have hz : ‖f i‖ ^ 2 = 0 := by
      have hp := i.property
      have hn := sq_nonneg ‖f i‖
      nlinarith
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hc := hw.fintype_card_le_finrank
  have hr : P.rank = Module.finrank ℂ (LinearMap.range L) := by
    simpa only [L, Matrix.toEuclideanLin_eq_toLin] using
      P.rank_eq_finrank_range_toLin (PiLp.basisFun 2 ℂ ι)
        (PiLp.basisFun 2 ℂ ι)
  rw [hr]
  simpa only [S, Fintype.card_subtype, Finset.mem_filter, Finset.mem_univ, true_and] using hc

end PRUMinMax


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace PRUMomentOperators

noncomputable local instance matrixL2Seminormed {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] : SeminormedAddCommGroup (Matrix ι κ ℂ) :=
  (Matrix.instL2OpNormedAddCommGroup : NormedAddCommGroup (Matrix ι κ ℂ)).toSeminormedAddCommGroup

attribute [local instance] qubitMatrixMeasurable qubitMatrixBorel

lemma rep_unitary {n : ℕ} (t : ℕ) (U : QMat n)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    PRUMoments.rep t U ∈ Matrix.unitaryGroup ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change PRUMoments.rep t U * (PRUMoments.rep t U)ᴴ = 1
  rw [← PRUHaar.rep_adjoint, ← PRUMoments.rep_mul]
  simpa only [PRUMoments.rep_one, Matrix.star_eq_conjTranspose] using congrArg (PRUMoments.rep t) hU.2

lemma continuous_rep {n : ℕ} (t : ℕ) : Continuous (PRUMoments.rep (n := n) t) :=
  continuous_pi fun x => continuous_pi fun y => PRUMoments.continuous_rep_entry t x y

lemma rep_integrable {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) : Integrable (PRUMoments.rep t) μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_rep t).aestronglyMeasurable
  exact hμ.mono fun U hU => (CStarRing.norm_of_mem_unitary (rep_unitary t U hU)).le

lemma moment_eq_integral {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    balancedUnitaryMoment μ t = ∫ U, PRUMoments.rep t U ∂μ := by
  ext x y
  let L : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
      ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M x y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact L.toContinuousLinearMap.integral_comp_comm (rep_integrable t μ hμ)

lemma moment_norm_le_one {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    specNorm (balancedUnitaryMoment μ t) ≤ 1 := by
  change ‖balancedUnitaryMoment μ t‖ ≤ 1
  rw [moment_eq_integral t μ hμ]
  simpa using norm_integral_le_of_norm_le_const (hμ.mono fun U hU =>
    (CStarRing.norm_of_mem_unitary (rep_unitary t U hU)).le)

lemma quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    |(star v ⬝ᵥ (M *ᵥ v)).re| ≤ specNorm M * PRUSpectralGap.normSq v := by
  let x : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hi := (Complex.abs_re_le_norm (inner ℂ x (Matrix.toEuclideanLin M x))).trans
    (norm_inner_le_norm x (Matrix.toEuclideanLin M x))
  have hn := M.l2_opNorm_mulVec x
  change ‖Matrix.toEuclideanLin M x‖ ≤ specNorm M * ‖x‖ at hn
  rw [← PRUMinMax.quadratic_eq] at hi
  calc
    _ ≤ ‖x‖ * ‖Matrix.toEuclideanLin M x‖ := by exact hi
    _ ≤ ‖x‖ * (specNorm M * ‖x‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = specNorm M * PRUSpectralGap.normSq v := by rw [show PRUSpectralGap.normSq v = ‖x‖ ^ 2 from PRUMinMax.normSq_eq x]; ring

lemma moment_haar_left {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    balancedUnitaryMoment μ t * balancedUnitaryMoment (haarLaw n) t =
      balancedUnitaryMoment (haarLaw n) t := by
  ext x y
  rw [Matrix.mul_apply]
  change (∑ i, (∫ U, PRUMoments.rep t U x i ∂μ) * _) = _
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum Finset.univ (fun i _ => (PRUMoments.rep_integrable t μ hμ x i).mul_const _)]
  calc
    _ = ∫ _ : QMat n, balancedUnitaryMoment (haarLaw n) t x y ∂μ := by
      apply integral_congr_ae
      exact hμ.mono fun U hU => congrFun (congrFun (PRUHaar.haar_left t U hU) x) y
    _ = _ := by simp

lemma moment_haar_right {n : ℕ} (t : ℕ) (μ : Measure (QMat n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    balancedUnitaryMoment (haarLaw n) t * balancedUnitaryMoment μ t =
      balancedUnitaryMoment (haarLaw n) t := by
  ext x y
  rw [Matrix.mul_apply]
  change (∑ i, _ * (∫ U, PRUMoments.rep t U i y ∂μ)) = _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun i _ => (PRUMoments.rep_integrable t μ hμ i y).const_mul _)]
  calc
    _ = ∫ _ : QMat n, balancedUnitaryMoment (haarLaw n) t x y ∂μ := by
      apply integral_congr_ae
      exact hμ.mono fun U hU => congrFun (congrFun (PRUHaar.haar_right t U hU) x) y
    _ = _ := by simp

end PRUMomentOperators


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms
open scoped Matrix ComplexConjugate BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace PRUQuadratic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def q (M : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ := (star v ⬝ᵥ (M *ᵥ v)).re
abbrev ns (v : ι → ℂ) : ℝ := PRUSpectralGap.normSq v

lemma q_add (A B : Matrix ι ι ℂ) (v : ι → ℂ) : q (A + B) v = q A v + q B v := by
  simp only [q, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
lemma q_sub (A B : Matrix ι ι ℂ) (v : ι → ℂ) : q (A - B) v = q A v - q B v := by
  simp only [q, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
lemma q_smul (a : ℝ) (A : Matrix ι ι ℂ) (v : ι → ℂ) : q (a • A) v = a * q A v := by
  simp only [q, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
lemma q_csmul (a : ℝ) (A : Matrix ι ι ℂ) (v : ι → ℂ) : q ((a : ℂ) • A) v = a * q A v := by
  simp only [q, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
lemma q_one (v : ι → ℂ) : q 1 v = ns v := by simp only [q, ns, PRUSpectralGap.normSq, Matrix.one_mulVec]
lemma q_zero (v : ι → ℂ) : q 0 v = 0 := by simp [q]

lemma q_nonneg (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (v : ι → ℂ) : 0 ≤ q A v :=
  (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1

lemma posSemidef_of_q (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (h : ∀ v, 0 ≤ q A v) : A.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hA,fun v => Complex.nonneg_iff.mpr ⟨h v,?_⟩⟩
  simpa only [RCLike.im_eq_complex_im] using (hA.im_star_dotProduct_mulVec_self v).symm

lemma q_abs_bound (A : Matrix ι ι ℂ) (v : ι → ℂ) : |q A v| ≤ specNorm A * ns v :=
  PRUMomentOperators.quadratic_bound A v

lemma projection_q (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (v : ι → ℂ) : q P v = ns (P *ᵥ v) := by
  unfold q ns PRUSpectralGap.normSq
  congr 1
  conv_rhs => rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hP.eq, hPP]

lemma projection_psd (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P * P = P) : P.PosSemidef :=
  posSemidef_of_q P hP (fun v => (projection_q P hP hPP v) ▸ PRUSpectralGap.normSq_nonneg _)

lemma eigen_q (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (i : ι) :
    q M ⇑(hM.eigenvectorBasis i) = hM.eigenvalues i := by
  simpa! only [q, RCLike.re_eq_complex_re] using (hM.eigenvalues_eq i).symm
lemma eigen_ns (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (i : ι) :
    ns ⇑(hM.eigenvectorBasis i) = 1 := by
  change PRUSpectralGap.normSq ⇑(hM.eigenvectorBasis i) = 1
  rw [PRUMinMax.normSq_eq (hM.eigenvectorBasis i), hM.eigenvectorBasis.norm_eq_one, one_pow]

lemma negative_eigenvalue (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (θ : ℝ)
    (hB : (M + (θ : ℂ) • 1).PosSemidef) (i : ι) (hi : hM.eigenvalues i < 0) :
    |hM.eigenvalues i| ≤ θ := by
  have h := q_nonneg _ hB ⇑(hM.eigenvectorBasis i)
  rw [q_add, q_csmul, q_one, eigen_q, eigen_ns, mul_one] at h
  rw [abs_of_neg hi]
  linarith

lemma mixture_count (C X Y : Matrix ι ι ℂ) (hC : C.PosSemidef)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (δ p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hg : specNorm (X - C) ≤ 1 - δ) (hy : specNorm Y ≤ 1) :
    let M := (1 - p) • X + p • Y
    let θ := 1 - (1 - p) * δ
    (∀ v, C *ᵥ v = 0 → q M v ≤ θ * ns v) ∧
    M.IsHermitian ∧
    (∀ hM : M.IsHermitian,
      (Finset.univ.filter fun i => θ < hM.eigenvalues i).card ≤ C.rank ∧
      ∀ i, hM.eigenvalues i < 0 → |hM.eigenvalues i| ≤ θ) ∧
    (M + (θ : ℂ) • 1).PosSemidef := by
  classical
  dsimp only
  let M := (1 - p) • X + p • Y
  let θ := 1 - (1 - p) * δ
  have hM : M.IsHermitian := (hX.smul (IsSelfAdjoint.all (1 - p))).add (hY.smul (IsSelfAdjoint.all p))
  have hxbound (v) : |q (X - C) v| ≤ (1 - δ) * ns v :=
    (q_abs_bound _ v).trans (mul_le_mul_of_nonneg_right hg (PRUSpectralGap.normSq_nonneg v))
  have hybound (v) : |q Y v| ≤ ns v := by
    simpa only [one_mul] using (q_abs_bound Y v).trans
      (mul_le_mul_of_nonneg_right hy (PRUSpectralGap.normSq_nonneg v))
  have hker (v) (hv : C *ᵥ v = 0) : q M v ≤ θ * ns v := by
    have hc : q C v = 0 := by simp [q,hv]
    have hx := (abs_le.mp (hxbound v)).2
    rw [q_sub,hc,sub_zero] at hx
    have hy' := (abs_le.mp (hybound v)).2
    have hp' : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    have h1 := mul_le_mul_of_nonneg_left hx hp'
    have h2 := mul_le_mul_of_nonneg_left hy' hp
    dsimp [M,θ]
    rw [q_add,q_smul,q_smul]
    nlinarith
  have hB : (M + (θ : ℂ) • 1).PosSemidef := by
    apply posSemidef_of_q _ (hM.add (Matrix.isHermitian_one.smul (by change conj (θ : ℂ) = (θ : ℂ); exact Complex.conj_ofReal θ : IsSelfAdjoint (θ : ℂ))))
    intro v
    have hx := (abs_le.mp (hxbound v)).1
    have hy' := (abs_le.mp (hybound v)).1
    have hc := q_nonneg C hC v
    rw [q_sub] at hx
    have h1 := mul_le_mul_of_nonneg_left (by linarith : -(1 - δ) * ns v ≤ q X v)
      (sub_nonneg.mpr hp1)
    have h2 := mul_le_mul_of_nonneg_left hy' hp
    rw [q_add,q_csmul,q_one]
    dsimp [M,θ]
    rw [q_add,q_smul,q_smul]
    nlinarith
  refine ⟨hker,hM,?_,hB⟩
  intro hM'
  exact ⟨PRUMinMax.count_le_rank M C hM' θ hker, negative_eigenvalue M hM' θ hB⟩

end PRUQuadratic


set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators

namespace PRUPhase

lemma coefficient_of_conjSuperop {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι ℂ) (h : conjSuperop U = conjSuperop V) (a b c d : ι) :
    U a c * conj (U b d) = V a c * conj (V b d) := by
  have h' := congrFun (congrFun (congrFun h (Matrix.single c d 1)) a) b
  simpa [conjSuperop, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, eq_comm] using h'

lemma conjSuperop_of_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι ℂ)
    (h : ∀ a b c d, U a c * conj (U b d) = V a c * conj (V b d)) :
    conjSuperop U = conjSuperop V := by
  funext X a b
  simp only [conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  simpa! only [mul_assoc, mul_comm, mul_left_comm, Complex.star_def] using congrArg (fun z : ℂ => z * X c d) (h a b c d)

lemma adjoint_conjSuperop {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι ℂ) (h : conjSuperop U = conjSuperop V) :
    conjSuperop Uᴴ = conjSuperop Vᴴ := by
  apply conjSuperop_of_coefficient
  intro a b c d
  simpa [Matrix.conjTranspose_apply, mul_comm] using coefficient_of_conjSuperop U V h d c b a

lemma rep_of_coefficient {n : ℕ} (t : ℕ) (U V : QMat n)
    (h : ∀ a b c d, U a c * conj (U b d) = V a c * conj (V b d)) :
    PRUMoments.rep t U = PRUMoments.rep t V := by
  ext x y
  simp only [PRUMoments.rep_apply, qubitTensorPower, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => h (x.1 i) (x.2 i) (y.1 i) (y.2 i))

lemma rep_of_conjSuperop {n : ℕ} (t : ℕ) (U V : QMat n)
    (h : conjSuperop U = conjSuperop V) : PRUMoments.rep t U = PRUMoments.rep t V :=
  rep_of_coefficient t U V (coefficient_of_conjSuperop U V h)

lemma edge_conjSuperop {n : ℕ} (i : Fin n) (U V : Matrix (Qubits 2) (Qubits 2) ℂ)
    (h : conjSuperop U = conjSuperop V) : conjSuperop (edgeLift i U) = conjSuperop (edgeLift i V) := by
  apply conjSuperop_of_coefficient
  intro a b c d
  change ((if ∀ q, q ≠ i → q ≠ nextWire i → a q = c q then U _ _ else 0) *
    conj (if ∀ q, q ≠ i → q ≠ nextWire i → b q = d q then U _ _ else 0)) =
    ((if ∀ q, q ≠ i → q ≠ nextWire i → a q = c q then V _ _ else 0) *
    conj (if ∀ q, q ≠ i → q ≠ nextWire i → b q = d q then V _ _ else 0))
  by_cases h1 : ∀ q, q ≠ i → q ≠ nextWire i → a q = c q
  · by_cases h2 : ∀ q, q ≠ i → q ≠ nextWire i → b q = d q
    · simp only [if_pos h1, if_pos h2]
      exact coefficient_of_conjSuperop U V h _ _ _ _
    · simp only [if_pos h1, if_neg h2, map_zero, mul_zero]
  · simp only [if_neg h1, zero_mul]

lemma edge_adjoint {n : ℕ} (i : Fin n) (U : Matrix (Qubits 2) (Qubits 2) ℂ) : edgeLift i Uᴴ = (edgeLift i U)ᴴ := by
  ext x y
  simp only [edgeLift, Matrix.of_apply, Matrix.conjTranspose_apply]
  have hh : (∀ q, q ≠ i → q ≠ nextWire i → x q = y q) ↔
      (∀ q, q ≠ i → q ≠ nextWire i → y q = x q) := by
    constructor <;> intro h q hq hr <;> exact (h q hq hr).symm
  simp only [hh]
  split_ifs <;> simp only [star_zero]

def invClass (n : ℕ) : Clifford.ProjectiveGroup n → Clifford.ProjectiveGroup n :=
  Quotient.map (fun U : Clifford.normalizer n => U⁻¹) (by
    intro U V h
    exact adjoint_conjSuperop U.val.val V.val.val h)

lemma invClass_mk (n : ℕ) (U : Clifford.normalizer n) :
    invClass n (Quotient.mk (Clifford.phaseSetoid n) U) = Quotient.mk (Clifford.phaseSetoid n) U⁻¹ := rfl

lemma invClass_involutive (n : ℕ) : Function.Involutive (invClass n) := by
  intro g
  refine Quotient.inductionOn g ?_
  intro U
  simp [invClass_mk, invClass, inv_inv]

lemma invClass_eq (n : ℕ) (g : Clifford.ProjectiveGroup n) :
    invClass n g = Quotient.mk (Clifford.phaseSetoid n) (Clifford.representative g)⁻¹ := by
  conv_lhs => rw [← Quotient.out_eq g]
  rfl

lemma representative_inv_relation (n : ℕ) (g : Clifford.ProjectiveGroup n) :
    conjSuperop (Clifford.representative (invClass n g)).val.val =
      conjSuperop ((Clifford.representative g).val.val)ᴴ := by
  have hq : (Clifford.phaseSetoid n).r (Clifford.representative (invClass n g))
      (Clifford.representative g)⁻¹ :=
    Quotient.exact ((Quotient.out_eq (invClass n g)).trans (invClass_eq n g))
  change conjSuperop (Clifford.representative (invClass n g)).val.val =
    conjSuperop ((Clifford.representative g)⁻¹).val.val at hq
  simpa only [Subgroup.coe_inv, ← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose] using hq

lemma inverse_rep (n t : ℕ) (g : Clifford.ProjectiveGroup n) :
    PRUMoments.rep t (Clifford.representative (invClass n g)).val.val =
      (PRUMoments.rep t (Clifford.representative g).val.val)ᴴ := by
  rw [← PRUHaar.rep_adjoint]
  exact rep_of_conjSuperop t _ _ (representative_inv_relation n g)

lemma inverse_edge_rep {n : ℕ} (t : ℕ) (i : Fin n) (g : Clifford.ProjectiveGroup 2) :
    PRUMoments.rep t (edgeLift i (Clifford.representative (invClass 2 g)).val.val) =
      (PRUMoments.rep t (edgeLift i (Clifford.representative g).val.val))ᴴ := by
  rw [← PRUHaar.rep_adjoint, ← edge_adjoint]
  exact rep_of_conjSuperop t _ _ (edge_conjSuperop i _ _ (representative_inv_relation 2 g))

end PRUPhase


set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators ENNReal

namespace PRUSymmetry
attribute [local instance] qubitMatrixMeasurable qubitMatrixBorel

lemma integral_sum_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {κ : Type*} (s : Finset κ) (F : κ → α) (f : α → ℂ) :
    ∫ x, f x ∂(∑ k ∈ s, Measure.dirac (F k)) = ∑ k ∈ s, f (F k) := by
  rw [integral_finsetSum_measure (fun i _ => (integrable_dirac (by simp)))]
  simp

lemma chi_entry (G : Finset (Clifford.ProjectiveGroup 2)) (n t : ℕ) (x y) :
    balancedUnitaryMoment (chiLaw G n) t x y =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ((G.card : ℝ)⁻¹ •
        ∑ g ∈ G, PRUMoments.rep t (edgeLift i (Clifford.representative g).val.val) x y) := by
  by_cases hG : G = ∅
  · subst G; simp [chiLaw, balancedUnitaryMoment]
  change (∫ U, PRUMoments.rep t U x y ∂chiLaw G n) = _
  unfold chiLaw
  simp only [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      integral_sum_dirac]
  · intro i _
    apply Integrable.smul_measure
    · exact integrable_finsetSum_measure.mpr fun g _ => integrable_dirac (by simp)
    · simp [hG]

lemma chi_isHermitian (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (n t : ℕ) : (balancedUnitaryMoment (chiLaw G n) t).IsHermitian := by
  classical
  ext x y
  rw [Matrix.conjTranspose_apply, chi_entry, chi_entry]
  simp only [star_smul, star_trivial, star_sum, Complex.star_def]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hinv (g) (hg : g ∈ G) : PRUPhase.invClass 2 g ∈ G := by
    rw [PRUPhase.invClass_eq]
    exact hG.2.1 g hg
  calc
    ∑ g ∈ G, conj (PRUMoments.rep t (edgeLift i (Clifford.representative g).val.val) y x) =
      ∑ g ∈ G, PRUMoments.rep t (edgeLift i (Clifford.representative (PRUPhase.invClass 2 g)).val.val) x y := by
        apply Finset.sum_congr rfl
        intro g _
        exact (congrFun (congrFun (PRUPhase.inverse_edge_rep t i g) x) y).symm
    _ = ∑ g ∈ G, PRUMoments.rep t (edgeLift i (Clifford.representative g).val.val) x y := by
      apply Finset.sum_bij (fun g _ => PRUPhase.invClass 2 g)
      · exact hinv
      · intro g hg h hh heq
        exact (PRUPhase.invClass_involutive 2).injective heq
      · intro g hg
        exact ⟨PRUPhase.invClass 2 g,hinv g hg,PRUPhase.invClass_involutive 2 g⟩
      · intro g hg; rfl

lemma rotZ_adjoint (φ : ℝ) : rotZ (-φ) = (rotZ φ)ᴴ := by
  simp only [rotZ, Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  simp only [Pi.star_apply]
  split_ifs <;> simp only [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  all_goals congr 1 <;> ring

lemma rotZ_periodic : Function.Periodic rotZ (2 * Real.pi) := by
  intro φ
  unfold rotZ
  congr 1
  funext x
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, add_mul]
  split_ifs
  · simp only [neg_add, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
  · rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma first_adjoint (n : ℕ) (U : QMat 1) : firstWireLift n Uᴴ = (firstWireLift n U)ᴴ := by
  by_cases hn : 0 < n
  · ext x y
    simp only [firstWireLift, dif_pos hn, Matrix.conjTranspose_apply]
    have hh : (∀ q : Fin n, q.val ≠ 0 → x q = y q) ↔ (∀ q : Fin n, q.val ≠ 0 → y q = x q) := by
      constructor <;> intro h q hq <;> exact (h q hq).symm
    simp only [hh]
    split_ifs <;> simp only [star_zero]
  · have heq (V : QMat 1) : firstWireLift n V = 1 := by ext; simp [firstWireLift, hn]
    rw [heq, heq, Matrix.conjTranspose_one]

lemma xi_entry (n t : ℕ) (x y) :
    balancedUnitaryMoment (xiLaw n) t x y = (2 * Real.pi)⁻¹ •
      ∫ φ in (0 : ℝ)..(2 * Real.pi), PRUMoments.rep t (firstWireLift n (rotZ φ)) x y := by
  change (∫ U, PRUMoments.rep t U x y ∂xiLaw n) = _
  unfold xiLaw
  have hm : AEMeasurable (fun φ : ℝ => firstWireLift n (rotZ φ))
      (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi))) :=
    (Continuous.measurable (γ := QMat n)
      ((PRUWalkLaws.continuous_firstWireLift n).comp PRUWalkLaws.continuous_rotZ)).aemeasurable
  rw [integral_map hm
    (PRUMoments.continuous_rep_entry t x y).aestronglyMeasurable]
  simp only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
  rw [integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le (by positivity)]

lemma xi_isHermitian (n t : ℕ) : (balancedUnitaryMoment (xiLaw n) t).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply, xi_entry, xi_entry]
  simp only [star_smul, star_trivial, Complex.star_def]
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), ← integral_conj]
  have h (φ : ℝ) : conj (PRUMoments.rep t (firstWireLift n (rotZ φ)) y x) =
      PRUMoments.rep t (firstWireLift n (rotZ (2 * Real.pi - φ))) x y := by
    rw [sub_eq_add_neg, add_comm, rotZ_periodic (-φ), rotZ_adjoint, first_adjoint, PRUHaar.rep_adjoint]
    rfl
  simp_rw [h]
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  simpa only [sub_self, sub_zero] using
    intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * Real.pi)
      (fun φ => PRUMoments.rep t (firstWireLift n (rotZ φ)) x y) (2 * Real.pi)

end PRUSymmetry


set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix ComplexConjugate BigOperators ENNReal

namespace PRUMixture
attribute [local instance] qubitMatrixMeasurable qubitMatrixBorel

lemma step_moment (G : Finset (Clifford.ProjectiveGroup 2)) (n m t : ℕ)
    (hG : G.Nonempty) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    balancedUnitaryMoment (stepLaw G n m) t =
      (1 - (m : ℝ)⁻¹) • balancedUnitaryMoment (chiLaw G n) t +
        (m : ℝ)⁻¹ • balancedUnitaryMoment (xiLaw n) t := by
  letI := PRUWalkLaws.chi_probability G n hG (by omega)
  letI := PRUWalkLaws.xi_probability n
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm'
  ext x y
  change (∫ U, PRUMoments.rep t U x y ∂stepLaw G n m) = _
  unfold stepLaw
  rw [integral_add_measure]
  · simp only [integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.mpr hp),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (m : ℝ)⁻¹)]
    rfl
  · exact (PRUMoments.rep_integrable t (chiLaw G n) (PRUWalkLaws.chi_unitary G n hn) x y).smul_measure
      ENNReal.ofReal_ne_top
  · exact (PRUMoments.rep_integrable t (xiLaw n) (PRUWalkLaws.xi_unitary n) x y).smul_measure
      ENNReal.ofReal_ne_top

lemma step_isHermitian (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (n m t : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    (balancedUnitaryMoment (stepLaw G n m) t).IsHermitian := by
  rw [step_moment G n m t ⟨_,hG.1⟩ hn hm]
  exact ((PRUSymmetry.chi_isHermitian G hG n t).smul (IsSelfAdjoint.all _)).add
    ((PRUSymmetry.xi_isHermitian n t).smul (IsSelfAdjoint.all _))

end PRUMixture

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms QuantumHMMR QAlgorithms.Papers.Independent.Extend50.P45
open scoped Matrix ComplexOrder BigOperators

theorem solution [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) (A : ℕ) (hA : 1 ≤ A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let p : ℝ := ((A * n ^ 2 : ℕ) : ℝ)⁻¹
      let M := balancedUnitaryMoment (stepLaw G n (A * n ^ 2)) t
      let MC := balancedUnitaryMoment (cliffordLaw n) t
      let θ : ℝ := 1 - (1 - p) * γ / n
      (∀ v, MC *ᵥ v = 0 → (star v ⬝ᵥ (M *ᵥ v)).re ≤ θ * (star v ⬝ᵥ v).re) ∧
      MC.rank ≤ Dt t ∧
      M.IsHermitian ∧
      (∀ hM : M.IsHermitian,
        (Finset.univ.filter fun i => θ < hM.eigenvalues i).card ≤ Dt t ∧
        ∀ i, hM.eigenvalues i < 0 → |hM.eigenvalues i| ≤ θ) ∧
      (M + (θ : ℂ) • (1 : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
        ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ)).PosSemidef  := by
  classical
  obtain ⟨nG,hgap⟩ := hga.2.2
  obtain ⟨nR,hrank⟩ := (QuantumHMMR.lemma_4_2 G hG).2.1 t ht
  refine ⟨max 2 (max nG nR),?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hm : 1 ≤ A * n ^ 2 := by
    have : 1 ≤ n ^ 2 := by nlinarith
    nlinarith
  have hp1 : (((A * n ^ 2 : ℕ) : ℝ)⁻¹) ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast hm)
  have hp0 : 0 ≤ (((A * n ^ 2 : ℕ) : ℝ)⁻¹) := by positivity
  obtain ⟨hC,hCC,_⟩ := (QuantumHMMR.lemma_4_2 G hG).1 t ht n
  have hX := PRUSymmetry.chi_isHermitian G hG n t
  have hY := PRUSymmetry.xi_isHermitian n t
  letI := PRUWalkLaws.xi_probability n
  have hy := PRUMomentOperators.moment_norm_le_one t (xiLaw n) (PRUWalkLaws.xi_unitary n)
  have hg := (hgap n (by omega)).1
  have hs := PRUQuadratic.mixture_count
    (balancedUnitaryMoment (cliffordLaw n) t) (balancedUnitaryMoment (chiLaw G n) t)
    (balancedUnitaryMoment (xiLaw n) t) (PRUQuadratic.projection_psd _ hC hCC)
    hX hY (γ / n) (((A * n ^ 2 : ℕ) : ℝ)⁻¹) hp0 hp1 hg hy
  dsimp only at hs ⊢
  rw [PRUMixture.step_moment G n (A * n ^ 2) t ⟨_,hG.1⟩ hn2 hm]
  have htheta : 1 - (1 - (((A * n ^ 2 : ℕ) : ℝ)⁻¹)) * γ / n =
      1 - (1 - (((A * n ^ 2 : ℕ) : ℝ)⁻¹)) * (γ / n) := by ring
  rw [htheta]
  have hr : (balancedUnitaryMoment (cliffordLaw n) t).rank ≤ Dt t :=
    (hrank n (by omega)).le
  refine ⟨hs.1,hr,hs.2.1,?_,hs.2.2.2⟩
  intro hM
  exact ⟨((hs.2.2.1 hM).1).trans hr,(hs.2.2.1 hM).2⟩


#print axioms solution
