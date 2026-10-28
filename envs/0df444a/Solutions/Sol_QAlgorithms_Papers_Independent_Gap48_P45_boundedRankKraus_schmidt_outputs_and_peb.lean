-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.boundedRankKraus_schmidt_outputs_and_peb
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:07:24.213983+00:00
-- url     : https://prove2.me/submissions/fa11c705-c737-4fbd-915b-a88627a6ee4e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
set_option Elab.async false

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology

attribute [local instance] Classical.propDecidable

namespace P45Aux
noncomputable local instance (priority := 1100) scH_nacg_1 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_1 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_1 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_1 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_1 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_1 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ns_1 (X : Type) : NormedSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_1 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scC_acg_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommGroup (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_acm_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_mod_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Module ℂ (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_top_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : TopologicalSpace (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_nacg_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : NormedAddCommGroup (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_ring_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Ring (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scC_sr_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Semiring (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scH_am_1 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_1 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_1 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_1 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_acg_1 (X Y : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_acm_1 (X Y : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_am_1 (X Y : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_azc_1 (X Y : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_top_1 (X Y : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_snacg_1 (X Y : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHE_ring_1 (X : Type) : Ring (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHE_nunas_1 (X : Type) : NonUnitalNonAssocSemiring (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_algR_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_algC_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℂ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_t2_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : T2Space (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_po_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : PartialOrder (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cstar_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : CStarAlgebra (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_sor_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_nsc_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cfcR_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_ncfcR_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_istR_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_smcR_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_star_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_tr_1 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsTopologicalRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_bcadd_1 (X : Type) : ContinuousAdd (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_btag_1 (X : Type) : IsTopologicalAddGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bccs_1 (X : Type) : ContinuousConstSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcs_1 (X : Type) : ContinuousSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bt2_1 (X : Type) : T2Space (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_badd_1 (X : Type) : Add (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bsmul_1 (X : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcladd_1 (X Y : Type) : Add (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsub_1 (X Y : Type) : Sub (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsmul_1 (X Y : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclmul_1 (X : Type) : Mul (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bclfun_1 (X Y : Type) : FunLike (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) (QAlgorithms.RealRegisters.Hilbert X) (QAlgorithms.RealRegisters.Hilbert Y) := inferInstance

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P18

lemma hasSum_coord {I ι : Type} {f : ι → Hilbert I} {x : Hilbert I} (h : HasSum f x) (i : I) :
    HasSum (fun n => f n i) (x i) :=
  h.map (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i) (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i).continuous

lemma hasSum_basis {I : Type} (x : Hilbert I) :
    HasSum (fun j => x j • (lp.single 2 j (1 : ℂ) : Hilbert I)) x := by
  have := lp.hasSum_single (E := fun _ : I => ℂ) (p := 2) (by simp) x
  convert this using 2 with j <;> first | rfl | rw [← lp.single_smul, smul_eq_mul, mul_one]

lemma op_ext {I L : Type} {A B : Hilbert I →L[ℂ] Hilbert L}
    (h : operatorCoeff A = operatorCoeff B) : A = B := by
  ext1 x
  have hA := (hasSum_basis x).map A A.continuous
  have hB := (hasSum_basis x).map B B.continuous
  refine hA.unique ?_
  convert hB using 1
  funext j
  simp only [Function.comp, map_smul]
  congr 1
  ext i
  have := congrFun (congrFun h i) j
  simpa [operatorCoeff] using this

lemma bO_eq {I : Type} {X : Matrix I I ℂ} {T : Hilbert I →L[ℂ] Hilbert I}
    (h : operatorCoeff T = X) : boundedOperator X = T := by
  have hex : ∃ A : Hilbert I →L[ℂ] Hilbert I, operatorCoeff A = X := ⟨T, h⟩
  unfold boundedOperator
  rw [dif_pos hex]
  exact op_ext (hex.choose_spec.trans h.symm)


lemma operatorCoeff_apply {I L : Type} (A : Hilbert I →L[ℂ] Hilbert L) (i : L) (j : I) :
    operatorCoeff A i j = (A (lp.single 2 j 1)) i := by
  simp only [operatorCoeff]

lemma inner_single_right' {I : Type} (v : Hilbert I) (j : I) :
    inner ℂ v (lp.single 2 j (1 : ℂ) : Hilbert I) = star (v j) := by
  rw [lp.inner_single_right]
  simp [mul_comm]

/-! ## Part B: nuclear operators -/

def rk {I : Type} (u v : Hilbert I) : Hilbert I →L[ℂ] Hilbert I :=
  (innerSL ℂ v).smulRight u

lemma rk_apply {I : Type} (u v x : Hilbert I) : rk u v x = inner ℂ v x • u := rfl

lemma norm_rk {I : Type} (u v : Hilbert I) : ‖rk u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [rk, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

def nucOp {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) : Hilbert I →L[ℂ] Hilbert I :=
  ∑' n, rk (e.left n) (e.right n)

lemma nucOp_summable {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    Summable (fun n => rk (e.left n) (e.right n)) :=
  Summable.of_norm_bounded e.summable (fun n => norm_rk _ _)

lemma nucOp_hasSum {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (x : Hilbert I) :
    HasSum (fun n => inner ℂ (e.right n) x • e.left n) (nucOp e x) := by
  have := (nucOp_summable e).hasSum.map (ContinuousLinearMap.apply ℂ (Hilbert I) x)
    (ContinuousLinearMap.continuous _)
  exact this

lemma nucOp_coeff {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    operatorCoeff (nucOp e) = X := by
  funext i j
  rw [operatorCoeff_apply, e.coefficients i j]
  have h := hasSum_coord (nucOp_hasSum e (lp.single 2 j 1)) i
  refine (HasSum.tsum_eq ?_).symm
  convert h using 1
  funext n
  rw [inner_single_right']
  simp [mul_comm]

lemma bO_nuc {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    boundedOperator X = nucOp e := bO_eq (nucOp_coeff e)

/-- Expansion from coefficientwise HasSum. -/
def mkExp {I : Type} {X : Matrix I I ℂ} (u v : ℕ → Hilbert I)
    (hs : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hX : ∀ i j, HasSum (fun n => u n i * star (v n j)) (X i j)) : NuclearExpansion X where
  left := u
  right := v
  summable := hs
  coefficients := fun i j => (hX i j).tsum_eq.symm


lemma coeff_summable {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) (i j : T) :
    Summable (fun n => e.left n i * star (e.right n j)) := by
  refine Summable.of_norm_bounded e.summable (fun n => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _)
    (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)

lemma coeff_hasSum {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) (i j : T) :
    HasSum (fun n => e.left n i * star (e.right n j)) (X i j) := by
  rw [e.coefficients i j]
  exact (coeff_summable e i j).hasSum


lemma conj_hasSum {I L : Type} (B : Hilbert I →L[ℂ] Hilbert L) {X : Matrix I I ℂ}
    (e : NuclearExpansion X) (i j : L) :
    HasSum (fun n => B (e.left n) i * star (B (e.right n) j)) (conjugateCoeff B X i j) := by
  rw [conjugateCoeff, operatorCoeff_apply, bO_nuc e]
  rw [show (B.comp ((nucOp e).comp (ContinuousLinearMap.adjoint B))) (lp.single 2 j 1) =
    B (nucOp e (ContinuousLinearMap.adjoint B (lp.single 2 j 1))) from rfl]
  have h1 := (nucOp_hasSum e ((ContinuousLinearMap.adjoint B) (lp.single 2 j 1))).map B B.continuous
  have h2 := hasSum_coord h1 i
  convert h2 using 1
  funext n
  simp only [Function.comp, map_smul]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_single_right']
  simp [mul_comm]


/-! ## Part C: Cauchy-Schwarz on coordinates and the trace formula -/
lemma coeff_bO {T : Type} {X : Matrix T T ℂ} (h : IsTraceClass X) :
    operatorCoeff (boundedOperator X) = X := by
  obtain ⟨e⟩ := h
  rw [bO_nuc e, nucOp_coeff e]

lemma coeff_sub {T : Type} (A B : Hilbert T →L[ℂ] Hilbert T) :
    operatorCoeff (A - B) = operatorCoeff A - operatorCoeff B := by
  funext i j
  simp [operatorCoeff]

lemma coeff_sum {T ι : Type} (s : Finset ι) (f : ι → Hilbert T →L[ℂ] Hilbert T) :
    operatorCoeff (∑ k ∈ s, f k) = ∑ k ∈ s, operatorCoeff (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext i j; simp [operatorCoeff]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    funext i j
    simp [operatorCoeff]

def opExp {T : Type} {D : Hilbert T →L[ℂ] Hilbert T} {u v : ℕ → Hilbert T}
    (h : QAlgorithms.Papers.Independent.Dependency50.P39.NuclearExpansion D u v) :
    NuclearExpansion (operatorCoeff D) :=
  mkExp u v h.1 (fun i j => by
    have h1 := hasSum_coord (h.2.map (ContinuousLinearMap.apply ℂ (Hilbert T) (lp.single 2 j (1 : ℂ)))
      (ContinuousLinearMap.continuous _)) i
    have hfun : (fun n => u n i * star (v n j)) = (fun n =>
        ((ContinuousLinearMap.apply ℂ (Hilbert T) (lp.single 2 j (1 : ℂ))) ∘
          (fun r => InnerProductSpace.rankOne ℂ (u r) (v r))) n i) := by
      funext n
      simp [InnerProductSpace.rankOne_apply, inner_single_right', mul_comm]
    rw [hfun, operatorCoeff_apply]
    exact h1)

lemma ts_le {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) :
    traceSize X ≤ ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖) := iInf_le _ e

lemma form_eq {T ι : Type} (S : Hilbert T →L[ℂ] Hilbert T) (s : Finset ι) (σ : ι → T)
    (w : ι → ℂ) :
    ∑ p ∈ s, ∑ q ∈ s, star (w p) * operatorCoeff S (σ p) (σ q) * w q =
      inner ℂ (∑ p ∈ s, w p • (lp.single 2 (σ p) (1:ℂ) : Hilbert T))
        (S (∑ q ∈ s, w q • (lp.single 2 (σ q) (1:ℂ) : Hilbert T))) := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, inner_smul_left, inner_smul_right, operatorCoeff_apply, lp.inner_single_left]
  simp
  ring


def PSDForms {T : Type} (X : Matrix T T ℂ) : Prop :=
  ∀ (s : Finset T) (z : T → ℂ), (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re

lemma pos_ext {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) (hX : PSDForms X)
    (y : Hilbert T) : (inner ℂ y (nucOp e y)).im = 0 ∧ 0 ≤ (inner ℂ y (nucOp e y)).re := by
  let S : Set ℂ := {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}
  have hS : IsClosed S :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hcont : Continuous (fun x : Hilbert T => inner ℂ x (nucOp e x)) :=
    continuous_id.inner (nucOp e).continuous
  have h0 : Filter.Tendsto (fun s : Finset T => ∑ j ∈ s, y j • (lp.single 2 j (1:ℂ) : Hilbert T))
      Filter.atTop (nhds y) := hasSum_basis y
  have htend := (hcont.tendsto y).comp h0
  refine hS.mem_of_tendsto htend (Filter.Eventually.of_forall (fun s => ?_))
  have := hX s (fun t => y t)
  show (inner ℂ (∑ j ∈ s, y j • (lp.single 2 j (1:ℂ) : Hilbert T))
      (nucOp e (∑ j ∈ s, y j • (lp.single 2 j (1:ℂ) : Hilbert T)))) ∈ S
  have hf := form_eq (nucOp e) s id (fun t => y t)
  rw [nucOp_coeff] at hf
  simp only [id] at hf
  rw [← hf]
  exact this

/-! ## B1: a density is a countable sum of rank-one positives (via the CFC square root) -/

lemma bO_pos {T : Type} (rho : State T) : (boundedOperator rho.coefficients).IsPositive := by
  obtain ⟨e⟩ := rho.density.1
  rw [bO_nuc e, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  obtain ⟨him, hre⟩ := pos_ext e rho.density.2.1 x
  have hz : inner ℂ (nucOp e x) x = inner ℂ x (nucOp e x) := by
    rw [← inner_conj_symm]; exact Complex.conj_eq_iff_im.mpr him
  rw [hz]
  refine ⟨?_, by simpa using hre⟩
  apply Complex.ext <;> simp [him]

lemma sa_coord {T : Type} {S : Hilbert T →L[ℂ] Hilbert T} (hS : IsSelfAdjoint S) (i a : T) :
    (S (lp.single 2 i (1 : ℂ))) a = star ((S (lp.single 2 a (1 : ℂ))) i) := by
  have h1 : (S (lp.single 2 i (1 : ℂ))) a = inner ℂ (lp.single 2 a (1 : ℂ) : Hilbert T)
      (S (lp.single 2 i (1 : ℂ))) := by
    rw [lp.inner_single_left]; simp
  rw [h1, ← ContinuousLinearMap.adjoint_inner_left, hS.adjoint_eq, inner_single_right']

lemma sqrt_exists {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hA : A.IsPositive) : ∃ S : E →L[ℂ] E, IsSelfAdjoint S ∧ S * S = A :=
  ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).isSelfAdjoint,
    CFC.sqrt_mul_sqrt_self A ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hA)⟩

lemma dens_decomp {T : Type} (rho : State T) : ∃ y : T → Hilbert T,
    (∀ i j, HasSum (fun a => y a i * star (y a j)) (rho.coefficients i j)) ∧
      HasSum (fun a => ‖y a‖ ^ 2) 1 := by
  set A := boundedOperator rho.coefficients with hA
  obtain ⟨S, hSsa, hSS⟩ := sqrt_exists A (bO_pos rho)
  have hcoef : ∀ i j, rho.coefficients i j = inner ℂ (S (lp.single 2 i (1 : ℂ)))
      (S (lp.single 2 j (1 : ℂ))) := by
    intro i j
    rw [← ContinuousLinearMap.adjoint_inner_right, hSsa.adjoint_eq]
    have : S (S (lp.single 2 j (1 : ℂ))) = A (lp.single 2 j (1 : ℂ)) := by
      rw [← hSS]; rfl
    rw [this, lp.inner_single_left]
    have h2 := congrFun (congrFun (coeff_bO rho.density.1) i) j
    rw [operatorCoeff_apply] at h2
    simp [← h2, hA]
  refine ⟨fun a => S (lp.single 2 a (1 : ℂ)), fun i j => ?_, ?_⟩
  · rw [hcoef]
    have h := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : T => ℂ) (S (lp.single 2 i (1 : ℂ))) (S (lp.single 2 j (1 : ℂ)))
    have hfun : ∀ a, (S (lp.single 2 a (1 : ℂ))) i * star ((S (lp.single 2 a (1 : ℂ))) j) =
        inner ℂ ((S (lp.single 2 i (1 : ℂ))) a) ((S (lp.single 2 j (1 : ℂ))) a) := by
      intro a
      rw [sa_coord hSsa i a, sa_coord hSsa j a]
      simp [mul_comm]
    simp_rw [← hfun] at h
    exact h
  · have hd := rho.density.2.2
    have hs : HasSum (fun i => (rho.coefficients i i).re) 1 := by
      rw [← hd.2]; exact hd.1.hasSum
    convert hs using 1
    funext a
    rw [hcoef]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _

/-! ## B2: slices, amplification, nonnegative double sums -/

lemma memℓp_two_iff' {T : Type} (f : T → ℂ) : Memℓp f 2 ↔ Summable (fun t => ‖f t‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simp

lemma hasSum_normSq {T : Type} (x : Hilbert T) : HasSum (fun t => ‖x t‖ ^ 2) (‖x‖ ^ 2) := by
  have := lp.hasSum_norm (by norm_num : 0 < (2:ℝ≥0∞).toReal) x
  simpa using this

def sliceV {T A : Type} (a : A) (x : Hilbert (T × A)) : Hilbert T :=
  ⟨fun t => x (t, a), by
    refine (memℓp_two_iff' (fun t => x (t, a))).mpr ?_
    exact (hasSum_normSq x).summable.comp_injective (i := fun t : T => ((t, a) : T × A))
      (fun u v h => by simpa using h)⟩

@[simp] lemma sliceV_apply {T A : Type} (a : A) (x : Hilbert (T × A)) (t : T) :
    sliceV a x t = x (t, a) := rfl

lemma joint1 {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {a : α → ℝ} {s : ℝ}
    (ha : ∀ x, HasSum (fun y => g (x, y)) (a x)) (hs : HasSum a s) : HasSum g s := by
  have hsum : Summable g := (summable_prod_of_nonneg hg).mpr
    ⟨fun x => (ha x).summable, by simpa only [(ha _).tsum_eq] using hs.summable⟩
  have h2 := hsum.hasSum.prod_fiberwise ha
  rw [hs.unique h2]
  exact hsum.hasSum

lemma joint2 {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {b : β → ℝ} {s : ℝ}
    (hb : ∀ y, HasSum (fun x => g (x, y)) (b y)) (hs : HasSum b s) : HasSum g s := by
  have h := joint1 (g ∘ Prod.swap) (fun p => hg _) hb hs
  have he := (Equiv.prodComm β α).hasSum_iff (f := g) (a := s)
  exact he.mp h

lemma dsum_swap {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {a : α → ℝ} {b : β → ℝ}
    {s : ℝ} (ha : ∀ x, HasSum (fun y => g (x, y)) (a x)) (hs : HasSum a s)
    (hb : ∀ y, HasSum (fun x => g (x, y)) (b y)) : HasSum b s := by
  have h := joint1 g hg ha hs
  have h' : HasSum (g ∘ Prod.swap) s := (Equiv.prodComm β α).hasSum_iff.mpr h
  exact h'.prod_fiberwise hb

lemma fiber_normSq {T A : Type} (x : Hilbert (T × A)) :
    HasSum (fun a => ‖sliceV a x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := hasSum_normSq x
  have h' : HasSum ((fun p : T × A => ‖x p‖ ^ 2) ∘ Prod.swap) (‖x‖ ^ 2) :=
    (Equiv.prodComm A T).hasSum_iff.mpr h
  exact h'.prod_fiberwise (fun a => by simpa using hasSum_normSq (sliceV a x))

lemma norm_sliceV_le' {T A : Type} (a : A) (x : Hilbert (T × A)) : ‖sliceV a x‖ ≤ ‖x‖ := by
  have h := le_hasSum (fiber_normSq x) a (fun _ _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

def ampV {I E K : Type} (V : Hilbert I →L[ℂ] Hilbert E) (y : Hilbert (I × K)) :
    Hilbert (E × K) :=
  ⟨fun p => V (sliceV p.2 y) p.1, by
    refine (memℓp_two_iff' _).mpr ?_
    have hs : Summable ((fun p : E × K => ‖V (sliceV p.2 y) p.1‖ ^ 2) ∘ Prod.swap) := by
      refine (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr ⟨fun c => ?_, ?_⟩
      · exact (hasSum_normSq (V (sliceV c y))).summable
      · simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]
        simp only [(hasSum_normSq _).tsum_eq]
        refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun c => ?_)
          ((fiber_normSq y).summable.mul_left (‖V‖ ^ 2))
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (V.le_opNorm _) 2
    exact (Equiv.prodComm K E).summable_iff.mp hs⟩

@[simp] lemma ampV_apply {I E K : Type} (V : Hilbert I →L[ℂ] Hilbert E) (y : Hilbert (I × K))
    (p : E × K) : ampV V y p = V (sliceV p.2 y) p.1 := rfl

lemma slice_ampV {I E K : Type} (V : Hilbert I →L[ℂ] Hilbert E) (y : Hilbert (I × K)) (c : K) :
    sliceV c (ampV V y) = V (sliceV c y) := by
  ext e; rfl

lemma kraus_norm {I J K : Type} {Phi : Matrix I I ℂ → Matrix J J ℂ}
    {V : K → (Hilbert I →L[ℂ] Hilbert J)} (h : IsKrausRepresentation Phi V) (x : Hilbert I) :
    HasSum (fun k => ‖V k x‖ ^ 2) (‖x‖ ^ 2) := by
  have h2 := (h.1 x).map (innerSL ℂ x) (innerSL ℂ x).continuous
  have h1 := Complex.reCLM.hasSum h2
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  convert h1 using 1
  · funext k
    simp only [Function.comp, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      Complex.reCLM_apply]
    rw [ContinuousLinearMap.adjoint_inner_right, norm_sq_eq_re_inner (𝕜 := ℂ)]
    rfl
  · rfl

lemma amp_kraus_norm {I J K κ : Type} {Phi : Matrix I I ℂ → Matrix J J ℂ}
    {V : κ → (Hilbert I →L[ℂ] Hilbert J)} (h : IsKrausRepresentation Phi V)
    (y : Hilbert (I × K)) : HasSum (fun k => ‖ampV (V k) y‖ ^ 2) (‖y‖ ^ 2) := by
  refine dsum_swap (fun p : K × κ => ‖V p.2 (sliceV p.1 y)‖ ^ 2) (fun _ => sq_nonneg _)
    (fun c => kraus_norm h (sliceV c y)) (fiber_normSq y) (fun k => ?_)
  have := fiber_normSq (ampV (V k) y)
  simpa only [slice_ampV] using this

/-! ## B3: Schmidt rank of an amplified vector -/

lemma memL2_bound {K : Type} (f : K → ℂ) (g : K → ℝ) (hg : Summable g)
    (h : ∀ c, ‖f c‖ ^ 2 ≤ g c) : Memℓp f 2 :=
  (memℓp_two_iff' f).mpr (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) h hg)

lemma fin_sum_range {m : ℕ} (G : Fin m → ℂ) :
    ∑ t : Fin m, G t = ∑ n ∈ Finset.range m, (if h : n < m then G ⟨n, h⟩ else 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => if h : n < m then G ⟨n, h⟩ else 0) m]
  simp

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE) in
lemma rankLE_mono {T A : Type} {m r : ℕ} (hmr : m ≤ r) {u : Hilbert (T × A)}
    (h : tensorRankLE m u) : tensorRankLE r u := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨fun t => if ht : t.1 < m then a ⟨t.1, ht⟩ else 0,
    fun t => if ht : t.1 < m then b ⟨t.1, ht⟩ else 0, fun i j => ?_⟩
  rw [hab, fin_sum_range, fin_sum_range]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hmr) (fun n hn hn' => ?_) |>.symm.trans ?_
  · simp only [Finset.mem_range] at hn hn'
    simp [hn, hn']
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_range] at hn
    simp [hn, lt_of_lt_of_le hn hmr]

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE) in
lemma rankLE_smul {T A : Type} {r : ℕ} (c : ℂ) {u : Hilbert (T × A)}
    (h : tensorRankLE r u) : tensorRankLE r (c • u) := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨fun t => c • a t, b, fun i j => ?_⟩
  rw [lp.coeFn_smul, Pi.smul_apply, hab, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

lemma lp_sum_apply {T ι : Type} (s : Finset ι) (f : ι → Hilbert T) (t : T) :
    (∑ k ∈ s, f k) t = ∑ k ∈ s, f k t := by
  rw [lp.coeFn_sum, Finset.sum_apply]

open QAlgorithms.Papers.Independent.Gap48.P45 (operatorRank) in
open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE) in
lemma amp_rank {I E K : Type} (V : Hilbert I →L[ℂ] Hilbert E) (r : ℕ)
    (hV : operatorRank V ≤ r) (y : Hilbert (I × K)) : tensorRankLE r (ampV V y) := by
  set R := LinearMap.range (V : Hilbert I →ₗ[ℂ] Hilbert E) with hR
  have hV' : Cardinal.toENat (Module.rank ℂ R) ≤ (r : ℕ∞) := hV
  have hlt : Module.rank ℂ R < Cardinal.aleph0 := by
    by_contra hc
    push_neg at hc
    have h1 : Cardinal.toENat (Module.rank ℂ R) = ⊤ := Cardinal.toENat_eq_top.mpr hc
    rw [h1] at hV'
    exact ENat.coe_ne_top r (top_le_iff.mp hV')
  haveI : FiniteDimensional ℂ R := Module.rank_lt_aleph0_iff.mp hlt
  have hfr : Module.finrank ℂ R ≤ r := by
    rw [← Module.finrank_eq_rank, Cardinal.toENat_nat] at hV'
    exact_mod_cast hV'
  set b := Module.finBasis ℂ R
  let φ : Fin (Module.finrank ℂ R) → (Hilbert I →L[ℂ] ℂ) := fun t =>
    ⟨(b.coord t).comp (V : Hilbert I →ₗ[ℂ] Hilbert E).rangeRestrict,
      (LinearMap.continuous_of_finiteDimensional (b.coord t)).comp
        (continuous_induced_rng.2 V.continuous)⟩
  have hexp : ∀ x, V x = ∑ t, φ t x • (b t : Hilbert E) := by
    intro x
    have h2 := congrArg Subtype.val (b.sum_repr ((V : Hilbert I →ₗ[ℂ] Hilbert E).rangeRestrict x))
    rw [Submodule.coe_sum] at h2
    calc V x = ((V : Hilbert I →ₗ[ℂ] Hilbert E).rangeRestrict x : Hilbert E) := rfl
      _ = _ := h2.symm
      _ = _ := Finset.sum_congr rfl (fun t _ => by rw [Submodule.coe_smul]; rfl)
  refine rankLE_mono hfr ⟨fun t => (b t : Hilbert E), fun t => ⟨fun c => φ t (sliceV c y),
    memL2_bound _ (fun c => ‖φ t‖ ^ 2 * ‖sliceV c y‖ ^ 2)
      ((fiber_normSq y).summable.mul_left _)
      (fun c => by rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ((φ t).le_opNorm _) 2)⟩,
    fun e c => ?_⟩
  rw [ampV_apply, hexp, lp_sum_apply]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-! ## B4: entrywise Kraus convergence -/

lemma coord_le {T : Type} (x : Hilbert T) (t : T) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by norm_num) x t

lemma coeff_le_ts {T : Type} (M : Matrix T T ℂ) (e f : T) :
    ENNReal.ofReal ‖M e f‖ ≤ traceSize M := by
  refine le_iInf (fun ex => ENNReal.ofReal_le_ofReal ?_)
  have hb : ∀ n, ‖ex.left n e * star (ex.right n f)‖ ≤ ‖ex.left n‖ * ‖ex.right n‖ := by
    intro n
    rw [norm_mul, norm_star]
    exact mul_le_mul (coord_le _ _) (coord_le _ _) (norm_nonneg _) (norm_nonneg _)
  rw [ex.coefficients e f]
  refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    ex.summable)).trans ?_
  exact Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    ex.summable) ex.summable

lemma kraus_entry {I J K : Type} {Phi : Matrix I I ℂ → Matrix J J ℂ}
    {V : K → (Hilbert I →L[ℂ] Hilbert J)} (h : IsKrausRepresentation Phi V)
    {X : Matrix I I ℂ} (hX : IsTraceClass X) (e f : J) :
    HasSum (fun k => conjugateCoeff (V k) X e f) (Phi X e f) := by
  have ht := h.2 X hX
  show Filter.Tendsto (fun s : Finset K => ∑ k ∈ s, conjugateCoeff (V k) X e f) Filter.atTop
    (nhds (Phi X e f))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ s : Finset K, ‖(∑ k ∈ s, conjugateCoeff (V k) X e f) - Phi X e f‖ =
      ‖(Phi X - ∑ k ∈ s, conjugateCoeff (V k) X) e f‖ := by
    intro s
    rw [norm_sub_rev]
    simp [Matrix.sum_apply]
  simp_rw [hb]
  have h2 : Filter.Tendsto (fun s : Finset K =>
      ENNReal.ofReal ‖(Phi X - ∑ k ∈ s, conjugateCoeff (V k) X) e f‖) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      (fun s => coeff_le_ts _ e f)
  have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
  rw [ENNReal.toReal_zero] at h3
  exact h3.congr (fun s => ENNReal.toReal_ofReal (norm_nonneg _))

/-! ## B5: a rank-one series converges in the bounded-operator trace norm -/

lemma rk_coeff {T : Type} (z : Hilbert T) : operatorCoeff (rk z z) = rankOne z := by
  funext i j
  rw [operatorCoeff_apply, rk_apply, inner_single_right', lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, rankOne, mul_comm]

lemma rk_eq {T : Type} (u v : Hilbert T) : InnerProductSpace.rankOne ℂ u v = rk u v := by
  ext1 x
  simp [InnerProductSpace.rankOne_apply, rk_apply]

lemma rk_summable {T : Type} (u v : ℕ → Hilbert T) (hs : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    Summable (fun n => rk (u n) (v n)) :=
  Summable.of_norm_bounded hs (fun n => norm_rk _ _)

lemma p39_ne {T : Type} (u v : ℕ → Hilbert T) (hs : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    QAlgorithms.Papers.Independent.Dependency50.P39.NuclearExpansion
      (∑' n, rk (u n) (v n)) u v := by
  refine ⟨hs, ?_⟩
  simp_rw [rk_eq]
  exact (rk_summable u v hs).hasSum

lemma ntn_nonneg {T : Type} (D : Hilbert T →L[ℂ] Hilbert T) :
    0 ≤ QAlgorithms.Papers.Independent.Dependency50.P39.nuclearTraceNorm D :=
  Real.sInf_nonneg (fun c ⟨u, v, _, hc⟩ => hc ▸ tsum_nonneg (fun _ => by positivity))

lemma ntn_le {T : Type} {D : Hilbert T →L[ℂ] Hilbert T} {u v : ℕ → Hilbert T}
    (h : QAlgorithms.Papers.Independent.Dependency50.P39.NuclearExpansion D u v) :
    QAlgorithms.Papers.Independent.Dependency50.P39.nuclearTraceNorm D ≤
      ∑' n, ‖u n‖ * ‖v n‖ :=
  csInf_le ⟨0, fun c ⟨u, v, _, hc⟩ => hc ▸ tsum_nonneg (fun _ => by positivity)⟩ ⟨u, v, h, rfl⟩

open QAlgorithms.Papers.Independent.Gap48.P45 (coefficientTraceHasSum) in
lemma rank1_series {T : Type} (Z : ℕ → Hilbert T) (hZ : Summable (fun n => ‖Z n‖ ^ 2))
    (Y : Matrix T T ℂ) (hY : ∀ i j, HasSum (fun n => Z n i * star (Z n j)) (Y i j)) :
    coefficientTraceHasSum (fun n => rankOne (Z n)) Y := by
  have hs : Summable (fun n => ‖Z n‖ * ‖Z n‖) := by simpa [sq] using hZ
  let eY : NuclearExpansion Y := mkExp Z Z hs hY
  have hbY : boundedOperator Y = ∑' n, rk (Z n) (Z n) := bO_nuc eY
  have hb1 : ∀ n, boundedOperator (rankOne (Z n)) = rk (Z n) (Z n) :=
    fun n => bO_eq (rk_coeff (Z n))
  refine ⟨⟨eY⟩, fun n => ⟨mkExp (fun m => if m = 0 then Z n else 0)
      (fun m => if m = 0 then Z n else 0)
      (summable_of_ne_finset_zero (s := {0}) (fun m hm => by
        simp only [Finset.mem_singleton] at hm
        simp [hm]))
      (fun i j => by
        have : rankOne (Z n) i j = (fun m : ℕ => (if m = 0 then Z n else 0) i *
            star ((if m = 0 then Z n else 0 : Hilbert T) j)) 0 := by simp [rankOne]
        show HasSum _ (rankOne (Z n) i j)
        rw [this]
        exact hasSum_single 0 (fun m hm => by simp [hm]))⟩, ?_⟩
  simp_rw [hb1, hbY]
  -- truncations
  let Zs : Finset ℕ → ℕ → Hilbert T := fun s n => if n ∈ s then Z n else 0
  let Zc : Finset ℕ → ℕ → Hilbert T := fun s n => if n ∈ s then 0 else Z n
  have hsS : ∀ s, Summable (fun n => ‖Zs s n‖ * ‖Zs s n‖) := fun s =>
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by
      by_cases h : n ∈ s <;> simp [Zs, h]; positivity) hs
  have hsC : ∀ s, Summable (fun n => ‖Zc s n‖ * ‖Zc s n‖) := fun s =>
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by
      by_cases h : n ∈ s <;> simp [Zc, h]; positivity) hs
  have hsCn : ∀ s, Summable (fun n => ‖-Zc s n‖ * ‖Zc s n‖) := fun s => by
    simpa using hsC s
  have e2 : ∀ s : Finset ℕ, ∑' n, rk (Zs s n) (Zs s n) = ∑ n ∈ s, rk (Z n) (Z n) := by
    intro s
    rw [tsum_eq_sum (s := s) (fun n hn => by simp [Zs, hn, rk])]
    exact Finset.sum_congr rfl (fun n hn => by simp [Zs, hn])
  have e3 : ∀ s : Finset ℕ, (∑ n ∈ s, rk (Z n) (Z n)) - ∑' n, rk (Z n) (Z n) =
      ∑' n, rk (-Zc s n) (Zc s n) := by
    intro s
    have hneg : (fun n => rk (-Zc s n) (Zc s n)) = fun n => -rk (Zc s n) (Zc s n) := by
      funext n; ext1 x; simp [rk_apply]
    have h1 : ∑' n, rk (Z n) (Z n) =
        ∑ n ∈ s, rk (Z n) (Z n) + ∑' n, rk (Zc s n) (Zc s n) := by
      rw [← e2, ← (rk_summable _ _ (hsS s)).tsum_add (rk_summable _ _ (hsC s))]
      congr 1
      funext n
      by_cases h : n ∈ s <;> simp [Zs, Zc, h, rk]
    rw [h1, hneg, tsum_neg]
    abel
  refine ⟨⟨Z, Z, p39_ne Z Z hs⟩, fun s => ⟨Zs s, Zs s, by rw [← e2]; exact p39_ne _ _ (hsS s)⟩,
    fun s => ⟨-Zc s, Zc s, by rw [e3]; exact p39_ne _ _ (hsCn s)⟩, ?_⟩
  -- the trace-norm tail
  set S := ∑' n, ‖Z n‖ * ‖Z n‖ with hS
  have hcost : ∀ s : Finset ℕ, ∑' n, ‖-Zc s n‖ * ‖Zc s n‖ = S - ∑ n ∈ s, ‖Z n‖ * ‖Z n‖ := by
    intro s
    have hf : (fun n => ‖-Zc s n‖ * ‖Zc s n‖) =
        fun n => ‖Z n‖ * ‖Z n‖ - (if n ∈ s then ‖Z n‖ * ‖Z n‖ else 0) := by
      funext n
      by_cases h : n ∈ s <;> simp [Zc, h]
    rw [hf, hs.tsum_sub (summable_of_ne_finset_zero (s := s) (fun n hn => by simp [hn])),
      tsum_eq_sum (f := fun n => if n ∈ s then ‖Z n‖ * ‖Z n‖ else 0) (s := s)
        (fun n hn => by simp [hn])]
    congr 1
    exact Finset.sum_congr rfl (fun n hn => by simp [hn])
  have htail : Filter.Tendsto (fun s : Finset ℕ => S - ∑ n ∈ s, ‖Z n‖ * ‖Z n‖) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : Finset ℕ => ∑ n ∈ s, ‖Z n‖ * ‖Z n‖) Filter.atTop
        (nhds S) := hs.hasSum
    have h2 := (tendsto_const_nhds (x := S)).sub h1
    rwa [sub_self] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun s => ntn_nonneg _) (fun s => ?_)
  rw [e3, ← hcost]
  exact ntn_le (p39_ne _ _ (hsCn s))

/-! ## B6: reindexing along an injection into ℕ, and the assembly -/

lemma ext_hasSum {T W α : Type} [Zero W] [AddCommMonoid α] [TopologicalSpace α] {g : T → ℕ}
    (hg : Function.Injective g) (y : T → W) (F : W → α) (hF : F 0 = 0) {a : α}
    (h : HasSum (fun t => F (y t)) a) :
    HasSum (fun n => F (Function.extend g y 0 n)) a := by
  have hf : ∀ n ∉ Set.range g, F (Function.extend g y 0 n) = 0 := by
    intro n hn
    rw [Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hn)]
    exact hF
  refine (hg.hasSum_iff hf).mp ?_
  simpa [Function.comp_def, hg.extend_apply] using h

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE) in
lemma single_rank {E K : Type} (r : ℕ) (hr : 0 < r) (e0 : E) (c0 : K) :
    tensorRankLE r (lp.single 2 (e0, c0) (1 : ℂ) : Hilbert (E × K)) := by
  refine rankLE_mono (m := 1) hr ⟨fun _ => lp.single 2 e0 (1 : ℂ), fun _ => lp.single 2 c0 (1 : ℂ),
    fun i j => ?_⟩
  simp only [lp.single_apply, Fin.sum_univ_one]
  by_cases hi : i = e0 <;> by_cases hj : j = c0 <;> simp [hi, hj, Pi.single_apply]

open QAlgorithms.Papers.Independent.Gap48.P45 in
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel) in
open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE) in
theorem childB {I E : Type} [Countable I] [Countable E] [Nonempty I] [Nonempty E]
    (Psi : Channel I E) (r : ℕ) (bound : ℕ∞) (hr : 0 < r)
    (hK : HasBoundedRankKraus Psi.val r bound) : CountableSchmidtOutputs Psi.val r := by
  obtain ⟨κ, hκ, V, -, hKr, hrk⟩ := hK
  intro K _ _ rho
  -- step 1: density decomposition indexed by ℕ
  obtain ⟨y0, hy0e, hy0n⟩ := dens_decomp rho
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (I × K)
  set y : ℕ → Hilbert (I × K) := Function.extend g y0 0 with hydef
  have hye : ∀ i j, HasSum (fun n => y n i * star (y n j)) (rho.coefficients i j) :=
    fun i j => ext_hasSum hg y0 (fun v : Hilbert (I × K) => v i * star (v j)) (by simp)
      (hy0e i j)
  have hyn : HasSum (fun n => ‖y n‖ ^ 2) 1 :=
    ext_hasSum hg y0 (fun v : Hilbert (I × K) => ‖v‖ ^ 2) (by simp) hy0n
  -- step 2: amplified vectors on κ × ℕ
  let z : κ × ℕ → Hilbert (E × K) := fun p => ampV (V p.1) (y p.2)
  have hzn : HasSum (fun p => ‖z p‖ ^ 2) 1 :=
    joint2 (fun p => ‖z p‖ ^ 2) (fun _ => sq_nonneg _) (fun n => amp_kraus_norm hKr (y n)) hyn
  have hzr : ∀ p, tensorRankLE r (z p) := fun p => amp_rank (V p.1) r (hrk p.1) (y p.2)
  set Y := tensorApply Psi.val rho.coefficients with hYdef
  have hze : ∀ P Q : E × K, HasSum (fun p => z p P * star (z p Q)) (Y P Q) := by
    intro P Q
    obtain ⟨e, a⟩ := P
    obtain ⟨f, b⟩ := Q
    have hbs : Summable (fun n => ‖sliceV a (y n)‖ * ‖sliceV b (y n)‖) :=
      Summable.of_nonneg_of_le (fun _ => by positivity)
        (fun n => by
          have := mul_le_mul (norm_sliceV_le' a (y n)) (norm_sliceV_le' b (y n))
            (norm_nonneg _) (norm_nonneg _)
          simpa [sq] using this)
        (by simpa [sq] using hyn.summable)
    let eab : NuclearExpansion (fun i j => rho.coefficients (i, a) (j, b)) :=
      mkExp (fun n => sliceV a (y n)) (fun n => sliceV b (y n)) hbs
        (fun i j => by simpa using hye (i, a) (j, b))
    have hk : HasSum (fun k => conjugateCoeff (V k) (fun i j => rho.coefficients (i, a) (j, b)) e f)
        (Y (e, a) (f, b)) := kraus_entry hKr ⟨eab⟩ e f
    have hfib : ∀ k, HasSum (fun n => z (k, n) (e, a) * star (z (k, n) (f, b)))
        (conjugateCoeff (V k) (fun i j => rho.coefficients (i, a) (j, b)) e f) :=
      fun k => conj_hasSum (V k) eab e f
    have hsum : Summable (fun p => z p (e, a) * star (z p (f, b))) :=
      Summable.of_norm_bounded hzn.summable (fun p => by
        rw [norm_mul, norm_star, sq]
        exact mul_le_mul (coord_le _ _) (coord_le _ _) (norm_nonneg _) (norm_nonneg _))
    have h2 := hsum.hasSum.prod_fiberwise hfib
    rw [hk.unique h2]
    exact hsum.hasSum
  -- step 3: reindex κ × ℕ to ℕ
  obtain ⟨g2, hg2⟩ := Countable.exists_injective_nat (κ × ℕ)
  set Z : ℕ → Hilbert (E × K) := Function.extend g2 z 0 with hZdef
  have hZn : HasSum (fun n => ‖Z n‖ ^ 2) 1 :=
    ext_hasSum hg2 z (fun v : Hilbert (E × K) => ‖v‖ ^ 2) (by simp) hzn
  have hZe : ∀ P Q, HasSum (fun n => Z n P * star (Z n Q)) (Y P Q) :=
    fun P Q => ext_hasSum hg2 z (fun v : Hilbert (E × K) => v P * star (v Q)) (by simp)
      (hze P Q)
  have hZr : ∀ n, Z n = 0 ∨ tensorRankLE r (Z n) := by
    intro n
    by_cases h : ∃ p, g2 p = n
    · obtain ⟨p, rfl⟩ := h
      right
      rw [hZdef, hg2.extend_apply]
      exact hzr p
    · left
      rw [hZdef, Function.extend_apply' _ _ _ h]
      rfl
  -- step 4: weights and unit vectors
  obtain ⟨e0⟩ := ‹Nonempty E›
  obtain ⟨c0⟩ := ‹Nonempty K›
  set u0 : Hilbert (E × K) := lp.single 2 (e0, c0) (1 : ℂ) with hu0def
  have hu0 : ‖u0‖ = 1 := by
    rw [hu0def, lp.norm_single (by norm_num)]
    simp
  refine ⟨fun n => ‖Z n‖ ^ 2, fun n => if Z n = 0 then u0 else ((‖Z n‖⁻¹ : ℝ) : ℂ) • Z n,
    fun n => sq_nonneg _, hZn, fun n => ?_, ?_⟩
  · by_cases h : Z n = 0
    · simp only [h, if_true]
      exact ⟨hu0, single_rank r hr e0 c0⟩
    · simp only [h, if_false]
      refine ⟨?_, rankLE_smul _ ((hZr n).resolve_left h)⟩
      have hn : ‖Z n‖ ≠ 0 := norm_ne_zero_iff.mpr h
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hn
  · have hfun : (fun n => (((‖Z n‖ ^ 2 : ℝ)) : ℂ) • rankOne (if Z n = 0 then u0 else
        ((‖Z n‖⁻¹ : ℝ) : ℂ) • Z n)) = fun n => rankOne (Z n) := by
      funext n
      by_cases h : Z n = 0
      · funext i j
        simp [h, rankOne]
      · simp only [h, if_false]
        have hn : ‖Z n‖ ≠ 0 := norm_ne_zero_iff.mpr h
        have hc : (((‖Z n‖ ^ 2 : ℝ)) : ℂ) * ((((‖Z n‖⁻¹ : ℝ)) : ℂ) *
            star (((‖Z n‖⁻¹ : ℝ)) : ℂ)) = 1 := by
          rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
          norm_cast
          field_simp
        funext i j
        simp only [rankOne, Matrix.smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          star_mul']
        linear_combination (Z n i * star (Z n j)) * hc
    rw [hfun]
    exact rank1_series Z hZn.summable Y hZe
def ileave {β : Type} (f g : ℕ → β) (m : ℕ) : β := if m % 2 = 0 then f (m / 2) else g (m / 2)

lemma ileave_even {β : Type} (f g : ℕ → β) (k : ℕ) : ileave f g (2 * k) = f k := by
  simp [ileave, show (2 * k) % 2 = 0 by omega, show 2 * k / 2 = k by omega]

lemma ileave_odd {β : Type} (f g : ℕ → β) (k : ℕ) : ileave f g (2 * k + 1) = g k := by
  simp [ileave, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]

def expAdd {T : Type} {X Y : Matrix T T ℂ} (e1 : NuclearExpansion X) (e2 : NuclearExpansion Y) :
    NuclearExpansion (X + Y) :=
  mkExp (ileave e1.left e2.left) (ileave e1.right e2.right)
    (by
      refine (HasSum.even_add_odd (f := fun m => ‖ileave e1.left e2.left m‖ *
        ‖ileave e1.right e2.right m‖) (m := ∑' n, ‖e1.left n‖ * ‖e1.right n‖)
        (m' := ∑' n, ‖e2.left n‖ * ‖e2.right n‖) ?_ ?_).summable
      · simpa only [ileave_even] using e1.summable.hasSum
      · simpa only [ileave_odd] using e2.summable.hasSum)
    (fun i j => by
      refine HasSum.even_add_odd (f := fun m => ileave e1.left e2.left m i *
        star (ileave e1.right e2.right m j)) ?_ ?_
      · simpa only [ileave_even] using coeff_hasSum e1 i j
      · simpa only [ileave_odd] using coeff_hasSum e2 i j)


/-! ## Child C: countable Schmidt outputs give r-partial entanglement breaking -/

def expNeg {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) : NuclearExpansion (-X) :=
  mkExp (fun n => -e.left n) e.right (by simpa using e.summable)
    (fun i j => by simpa [neg_mul] using (coeff_hasSum e i j).neg)

lemma expNeg_tsum {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) :
    ∑' n, ‖(expNeg e).left n‖ * ‖(expNeg e).right n‖ = ∑' n, ‖e.left n‖ * ‖e.right n‖ := by
  change ∑' n, ‖-e.left n‖ * ‖e.right n‖ = _
  simp

def expRk {T : Type} (c : ℂ) (u : Hilbert T) : NuclearExpansion (c • rankOne u) :=
  mkExp (fun n => if n = 0 then c • u else 0) (fun n => if n = 0 then u else 0)
    (summable_of_ne_finset_zero (s := {0}) (fun n hn => by
      simp only [Finset.mem_singleton] at hn
      simp [hn]))
    (fun i j => by
      have : (c • rankOne u) i j = (fun n : ℕ => (if n = 0 then c • u else 0) i *
          star ((if n = 0 then u else 0) j)) 0 := by
        simp [rankOne, mul_assoc]
      rw [this]
      exact hasSum_single 0 (fun n hn => by simp [hn]))

lemma expRk_tsum {T : Type} (c : ℂ) (u : Hilbert T) :
    ∑' n, ‖(expRk c u).left n‖ * ‖(expRk c u).right n‖ = ‖c‖ * ‖u‖ * ‖u‖ := by
  change ∑' n : ℕ, ‖(if n = 0 then c • u else 0)‖ * ‖(if n = 0 then u else 0 : Hilbert T)‖ = _
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp [norm_smul]

lemma expAdd_tsum {T : Type} {X Y : Matrix T T ℂ} (e1 : NuclearExpansion X)
    (e2 : NuclearExpansion Y) :
    ∑' m, ‖(expAdd e1 e2).left m‖ * ‖(expAdd e1 e2).right m‖ =
      (∑' n, ‖e1.left n‖ * ‖e1.right n‖) + ∑' n, ‖e2.left n‖ * ‖e2.right n‖ := by
  change ∑' m, ‖ileave e1.left e2.left m‖ * ‖ileave e1.right e2.right m‖ = _
  exact (HasSum.even_add_odd (f := fun m => ‖ileave e1.left e2.left m‖ *
        ‖ileave e1.right e2.right m‖)
      (by simpa only [ileave_even] using e1.summable.hasSum)
      (by simpa only [ileave_odd] using e2.summable.hasSum)).tsum_eq

open QAlgorithms.Papers.Independent.Gap48.P45 in
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel) in
open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE) in
theorem childC {I E : Type} [Countable I] [Countable E] [Nonempty I] [Nonempty E]
    (Psi : Channel I E) (r : ℕ) (_hr : 0 < r)
    (hS : CountableSchmidtOutputs Psi.val r) : PartiallyEntanglementBreaking Psi.val r := by
  intro K _ _ rho
  obtain ⟨w, u, hw0, hw1, hu, hT⟩ := hS K rho
  set Y := tensorApply Psi.val rho.coefficients with hYdef
  obtain ⟨hYtc, hXtc, hTS⟩ := hT
  obtain ⟨_, _, hdtc, hlim⟩ := hTS
  intro ε hε
  have hev1 : ∀ᶠ s in Filter.atTop, QAlgorithms.Papers.Independent.Dependency50.P39.nuclearTraceNorm
      ((∑ i ∈ s, boundedOperator ((w i : ℂ) • rankOne (u i))) - boundedOperator Y) < ε / 2 :=
    hlim (Iio_mem_nhds (by linarith))
  have hev2 : ∀ᶠ s in Filter.atTop, |(∑ i ∈ s, w i) - 1| < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hw1) (ε / 2) (by linarith)
    filter_upwards [h] with s hs
    simpa [Real.dist_eq] using hs
  obtain ⟨s, hs1, hs2⟩ := (hev1.and hev2).exists
  set D := (∑ i ∈ s, boundedOperator ((w i : ℂ) • rankOne (u i))) - boundedOperator Y with hDdef
  have hs1' : sInf {c : ℝ | ∃ a b : ℕ → Hilbert (E × K),
      QAlgorithms.Papers.Independent.Dependency50.P39.NuclearExpansion D a b ∧
        c = ∑' n, ‖a n‖ * ‖b n‖} < ε / 2 := hs1
  obtain ⟨c, ⟨a, b, hab, rfl⟩, hc⟩ := exists_lt_of_csInf_lt
    (by obtain ⟨a, b, h⟩ := hdtc s; exact ⟨_, a, b, h, rfl⟩) hs1'
  have hDc : operatorCoeff D = (∑ i ∈ s, (w i : ℂ) • rankOne (u i)) - Y := by
    rw [hDdef, coeff_sub, coeff_sum, coeff_bO hYtc]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => coeff_bO (hXtc i))
  set c' : ℝ := 1 - ∑ i ∈ s, w i with hc'
  have hsle : ∑ i ∈ s, w i ≤ 1 := sum_le_hasSum s (fun i _ => hw0 i) hw1
  have hc'0 : 0 ≤ c' := by rw [hc']; linarith
  have hc'lt : c' < ε / 2 := by
    have := (abs_lt.mp hs2).1
    rw [hc']; linarith
  -- the convex combination
  let N : ℕ := s.sup id + 1
  have hN : N ∉ s := fun h => by
    have := Finset.le_sup (f := id) h
    simp only [id] at this
    omega
  let wt : ℕ → ℝ := fun i => if i = N then c' else w i
  let zt : ℕ → Matrix (E × K) (E × K) ℂ := fun i => if i = N then rankOne (u 0) else rankOne (u i)
  have hmem := (convex_convexHull ℝ {X : Matrix (E × K) (E × K) ℂ |
        ∃ u : Hilbert (E × K), ‖u‖ = 1 ∧ tensorRankLE r u ∧ X = rankOne u}).sum_mem
      (t := insert N s) (w := wt) (z := zt)
      (fun i _ => by
        simp only [wt]
        split_ifs
        · exact hc'0
        · exact hw0 i)
      (by
        rw [Finset.sum_insert hN]
        simp only [wt, if_pos rfl]
        rw [Finset.sum_congr rfl (fun i hi => if_neg (show i ≠ N from fun h => hN (h ▸ hi)))]
        rw [hc']; ring)
      (fun i _ => by
        apply subset_convexHull
        simp only [zt]
        split_ifs
        · exact ⟨u 0, (hu 0).1, (hu 0).2, rfl⟩
        · exact ⟨u i, (hu i).1, (hu i).2, rfl⟩)
  refine ⟨_, hmem, ?_⟩
  have hZ : ∑ i ∈ insert N s, wt i • zt i =
      (∑ i ∈ s, (w i : ℂ) • rankOne (u i)) + (c' : ℂ) • rankOne (u 0) := by
    rw [Finset.sum_insert hN, add_comm]
    simp only [wt, zt, if_pos rfl]
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [if_neg (show i ≠ N from fun h => hN (h ▸ hi)), if_neg (show i ≠ N from fun h => hN (h ▸ hi))])]
    congr 1
  have hdiff : Y - ∑ i ∈ insert N s, wt i • zt i =
      -(operatorCoeff D) + (-(c' : ℂ)) • rankOne (u 0) := by
    rw [hZ, hDc, neg_smul]
    abel
  rw [hdiff]
  let e := expAdd (expNeg (opExp hab)) (expRk (-(c' : ℂ)) (u 0))
  refine lt_of_le_of_lt (ts_le e) ?_
  rw [expAdd_tsum, expNeg_tsum, expRk_tsum]
  change ENNReal.ofReal ((∑' n, ‖a n‖ * ‖b n‖) + _) < _
  rw [ENNReal.ofReal_lt_ofReal_iff hε]
  have hu0 : ‖u 0‖ = 1 := (hu 0).1
  rw [hu0, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc'0]
  linarith

end P45Aux

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology

attribute [local instance] Classical.propDecidable

namespace P45D

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P18
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond
  boundedConjugation)

/-! Helpers copied from scratch/probe/176d3efb_childB.lean (P45Aux). -/
lemma hasSum_coord {I ι : Type} {f : ι → Hilbert I} {x : Hilbert I} (h : HasSum f x) (i : I) :
    HasSum (fun n => f n i) (x i) :=
  h.map (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i) (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i).continuous

lemma hasSum_basis {I : Type} (x : Hilbert I) :
    HasSum (fun j => x j • (lp.single 2 j (1 : ℂ) : Hilbert I)) x := by
  have := lp.hasSum_single (E := fun _ : I => ℂ) (p := 2) (by simp) x
  convert this using 2 with j <;> first | rfl | rw [← lp.single_smul, smul_eq_mul, mul_one]

lemma op_ext {I L : Type} {A B : Hilbert I →L[ℂ] Hilbert L}
    (h : operatorCoeff A = operatorCoeff B) : A = B := by
  ext1 x
  have hA := (hasSum_basis x).map A A.continuous
  have hB := (hasSum_basis x).map B B.continuous
  refine hA.unique ?_
  convert hB using 1
  funext j
  simp only [Function.comp, map_smul]
  congr 1
  ext i
  have := congrFun (congrFun h i) j
  simpa [operatorCoeff] using this

lemma bO_eq {I : Type} {X : Matrix I I ℂ} {T : Hilbert I →L[ℂ] Hilbert I}
    (h : operatorCoeff T = X) : boundedOperator X = T := by
  have hex : ∃ A : Hilbert I →L[ℂ] Hilbert I, operatorCoeff A = X := ⟨T, h⟩
  unfold boundedOperator
  rw [dif_pos hex]
  exact op_ext (hex.choose_spec.trans h.symm)


lemma operatorCoeff_apply {I L : Type} (A : Hilbert I →L[ℂ] Hilbert L) (i : L) (j : I) :
    operatorCoeff A i j = (A (lp.single 2 j 1)) i := by
  simp only [operatorCoeff]

lemma inner_single_right' {I : Type} (v : Hilbert I) (j : I) :
    inner ℂ v (lp.single 2 j (1 : ℂ) : Hilbert I) = star (v j) := by
  rw [lp.inner_single_right]
  simp [mul_comm]

/-! ## Part B: nuclear operators -/
lemma memℓp_two_iff' {T : Type} (f : T → ℂ) : Memℓp f 2 ↔ Summable (fun t => ‖f t‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simp

lemma hasSum_normSq {T : Type} (x : Hilbert T) : HasSum (fun t => ‖x t‖ ^ 2) (‖x‖ ^ 2) := by
  have := lp.hasSum_norm (by norm_num : 0 < (2:ℝ≥0∞).toReal) x
  simpa using this

def sliceV {T A : Type} (a : A) (x : Hilbert (T × A)) : Hilbert T :=
  ⟨fun t => x (t, a), by
    refine (memℓp_two_iff' (fun t => x (t, a))).mpr ?_
    exact (hasSum_normSq x).summable.comp_injective (i := fun t : T => ((t, a) : T × A))
      (fun u v h => by simpa using h)⟩

@[simp] lemma sliceV_apply {T A : Type} (a : A) (x : Hilbert (T × A)) (t : T) :
    sliceV a x t = x (t, a) := rfl

lemma joint1 {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {a : α → ℝ} {s : ℝ}
    (ha : ∀ x, HasSum (fun y => g (x, y)) (a x)) (hs : HasSum a s) : HasSum g s := by
  have hsum : Summable g := (summable_prod_of_nonneg hg).mpr
    ⟨fun x => (ha x).summable, by simpa only [(ha _).tsum_eq] using hs.summable⟩
  have h2 := hsum.hasSum.prod_fiberwise ha
  rw [hs.unique h2]
  exact hsum.hasSum

lemma joint2 {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {b : β → ℝ} {s : ℝ}
    (hb : ∀ y, HasSum (fun x => g (x, y)) (b y)) (hs : HasSum b s) : HasSum g s := by
  have h := joint1 (g ∘ Prod.swap) (fun p => hg _) hb hs
  have he := (Equiv.prodComm β α).hasSum_iff (f := g) (a := s)
  exact he.mp h

lemma dsum_swap {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {a : α → ℝ} {b : β → ℝ}
    {s : ℝ} (ha : ∀ x, HasSum (fun y => g (x, y)) (a x)) (hs : HasSum a s)
    (hb : ∀ y, HasSum (fun x => g (x, y)) (b y)) : HasSum b s := by
  have h := joint1 g hg ha hs
  have h' : HasSum (g ∘ Prod.swap) s := (Equiv.prodComm β α).hasSum_iff.mpr h
  exact h'.prod_fiberwise hb

lemma fiber_normSq {T A : Type} (x : Hilbert (T × A)) :
    HasSum (fun a => ‖sliceV a x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := hasSum_normSq x
  have h' : HasSum ((fun p : T × A => ‖x p‖ ^ 2) ∘ Prod.swap) (‖x‖ ^ 2) :=
    (Equiv.prodComm A T).hasSum_iff.mpr h
  exact h'.prod_fiberwise (fun a => by simpa using hasSum_normSq (sliceV a x))

lemma norm_sliceV_le' {T A : Type} (a : A) (x : Hilbert (T × A)) : ‖sliceV a x‖ ≤ ‖x‖ := by
  have h := le_hasSum (fiber_normSq x) a (fun _ _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

def ampV {I E K : Type} (V : Hilbert I →L[ℂ] Hilbert E) (y : Hilbert (I × K)) :
    Hilbert (E × K) :=
  ⟨fun p => V (sliceV p.2 y) p.1, by
    refine (memℓp_two_iff' _).mpr ?_
    have hs : Summable ((fun p : E × K => ‖V (sliceV p.2 y) p.1‖ ^ 2) ∘ Prod.swap) := by
      refine (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr ⟨fun c => ?_, ?_⟩
      · exact (hasSum_normSq (V (sliceV c y))).summable
      · simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]
        simp only [(hasSum_normSq _).tsum_eq]
        refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun c => ?_)
          ((fiber_normSq y).summable.mul_left (‖V‖ ^ 2))
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (V.le_opNorm _) 2
    exact (Equiv.prodComm K E).summable_iff.mp hs⟩

@[simp] lemma ampV_apply {I E K : Type} (V : Hilbert I →L[ℂ] Hilbert E) (y : Hilbert (I × K))
    (p : E × K) : ampV V y p = V (sliceV p.2 y) p.1 := rfl

lemma slice_ampV {I E K : Type} (V : Hilbert I →L[ℂ] Hilbert E) (y : Hilbert (I × K)) (c : K) :
    sliceV c (ampV V y) = V (sliceV c y) := by
  ext e; rfl


/-! ADual groundwork: pure states and the Stinespring form of a complementary pair. -/






lemma sliceV_add {T A : Type} (c : A) (y z : Hilbert (T × A)) :
    sliceV c (y + z) = sliceV c y + sliceV c z := by ext t; rfl

lemma sliceV_smul {T A : Type} (c : A) (a : ℂ) (y : Hilbert (T × A)) :
    sliceV c (a • y) = a • sliceV c y := by ext t; rfl

lemma norm_ampV_le {I E K : Type} (V : Hilbert I →L[ℂ] Hilbert E) (y : Hilbert (I × K)) :
    ‖ampV V y‖ ≤ ‖V‖ * ‖y‖ := by
  have h1 := fiber_normSq (ampV V y)
  have h2 := (fiber_normSq y).mul_left (‖V‖ ^ 2)
  have hle : ‖ampV V y‖ ^ 2 ≤ (‖V‖ * ‖y‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun c => ?_) h1 h2
    rw [slice_ampV, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (V.le_opNorm _) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle

/-- `B ⊗ 1` on `Hilbert (J × E)` as a bounded operator. -/
def ampL {J E : Type} (B : Hilbert J →L[ℂ] Hilbert J) : Hilbert (J × E) →L[ℂ] Hilbert (J × E) :=
  LinearMap.mkContinuous
    { toFun := ampV (K := E) B
      map_add' := fun y z => by
        ext p
        simp only [ampV_apply, sliceV_add, map_add]
        rfl
      map_smul' := fun a y => by
        ext p
        simp only [ampV_apply, sliceV_smul, map_smul, RingHom.id_apply]
        rfl }
    ‖B‖ (fun y => norm_ampV_le B y)

@[simp] lemma ampL_apply {J E : Type} (B : Hilbert J →L[ℂ] Hilbert J) (y : Hilbert (J × E)) :
    ampL B y = ampV B y := rfl


/-! ## ADual part 1: row slices, the partial-trace operator and its trace pairing -/

def rowV {T A : Type} (t : T) (x : Hilbert (T × A)) : Hilbert A :=
  ⟨fun a => x (t, a), by
    refine (memℓp_two_iff' (fun a => x (t, a))).mpr ?_
    exact (hasSum_normSq x).summable.comp_injective (i := fun a : A => ((t, a) : T × A))
      (fun u v h => by simpa using h)⟩

@[simp] lemma rowV_apply {T A : Type} (t : T) (x : Hilbert (T × A)) (a : A) :
    rowV t x a = x (t, a) := rfl












/-! ## ADual part 2: polarization and the Stinespring form of the dual -/














/-! ## AKraus part 1: bra operators `(<ψ| ⊗ 1)`, `A†A = Φ^*(|ψ><ψ|)` and the rank identity -/

open QAlgorithms.Papers.Independent.Gap48.P45 (operatorRank)

def rk {I : Type} (u v : Hilbert I) : Hilbert I →L[ℂ] Hilbert I := (innerSL ℂ v).smulRight u

lemma rk_apply {I : Type} (u v x : Hilbert I) : rk u v x = inner ℂ v x • u := rfl


/-- `(<ψ| ⊗ 1) y`, coordinatewise `⟪ψ, y_e⟫`. -/
def braV {J E : Type} (psi : Hilbert J) (y : Hilbert (J × E)) : Hilbert E :=
  ⟨fun e => inner ℂ psi (sliceV e y), by
    refine (memℓp_two_iff' _).mpr ?_
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun e => ?_)
      ((fiber_normSq y).summable.mul_left (‖psi‖ ^ 2))
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2⟩

@[simp] lemma braV_apply {J E : Type} (psi : Hilbert J) (y : Hilbert (J × E)) (e : E) :
    braV psi y e = inner ℂ psi (sliceV e y) := rfl

lemma norm_braV_le {J E : Type} (psi : Hilbert J) (y : Hilbert (J × E)) :
    ‖braV psi y‖ ≤ ‖psi‖ * ‖y‖ := by
  have h1 := hasSum_normSq (braV psi y)
  have h2 := (fiber_normSq y).mul_left (‖psi‖ ^ 2)
  have hle : ‖braV psi y‖ ^ 2 ≤ (‖psi‖ * ‖y‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun e => ?_) h1 h2
    rw [braV_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle

def braL {J E : Type} (psi : Hilbert J) : Hilbert (J × E) →L[ℂ] Hilbert E :=
  LinearMap.mkContinuous
    { toFun := braV psi
      map_add' := fun y z => by
        ext e
        simp only [braV_apply, sliceV_add, inner_add_right]
        rfl
      map_smul' := fun a y => by
        ext e
        simp only [braV_apply, sliceV_smul, inner_smul_right, RingHom.id_apply]
        rfl }
    ‖psi‖ (fun y => norm_braV_le psi y)

@[simp] lemma braL_apply {J E : Type} (psi : Hilbert J) (y : Hilbert (J × E)) :
    braL psi y = braV psi y := rfl






/-! ## AKraus part 2 (generic): `Σ ‖A_k u‖² = ‖u‖²` gives strong convergence of `Σ A_k†A_k` to `1` -/

section KrausStrong

variable {K H F : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



end KrausStrong

/-- K2b: with slices of `V u` fixed by `P` and `{ψ_k}` a Parseval frame for `P` (quadratic form),
`Σ_k ‖(<ψ_k| ⊗ 1) V u‖² = ‖u‖²`. -/
lemma kraus_norm {I J E K : Type} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (P : Hilbert J →L[ℂ] Hilbert J) (psi : K → Hilbert J)
    (hpsi : ∀ x, HasSum (fun k => ‖inner ℂ (psi k) x‖ ^ 2) (inner ℂ x (P x)).re)
    (hsl : ∀ u e, P (sliceV e (V u)) = sliceV e (V u)) (u : Hilbert I) :
    HasSum (fun k => ‖((braL (E := E) (psi k)).comp V.toContinuousLinearMap) u‖ ^ 2) (‖u‖ ^ 2) := by
  have ha : ∀ e : E, HasSum (fun k => ‖inner ℂ (psi k) (sliceV e (V u))‖ ^ 2)
      (‖sliceV e (V u)‖ ^ 2) := by
    intro e
    have h := hpsi (sliceV e (V u))
    have h2 : (inner ℂ (sliceV e (V u)) (sliceV e (V u))).re = ‖sliceV e (V u)‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    rwa [hsl u e, h2] at h
  have hs : HasSum (fun e : E => ‖sliceV e (V u)‖ ^ 2) (‖u‖ ^ 2) := by
    have h := fiber_normSq (V u)
    rwa [LinearIsometry.norm_map] at h
  have hb : ∀ k, HasSum (fun e : E => ‖inner ℂ (psi k) (sliceV e (V u))‖ ^ 2)
      (‖((braL (E := E) (psi k)).comp V.toContinuousLinearMap) u‖ ^ 2) := by
    intro k
    exact hasSum_normSq (braV (psi k) (V u))
  exact dsum_swap (fun p : E × K => ‖inner ℂ (psi p.2) (sliceV p.1 (V u))‖ ^ 2)
    (fun _ => sq_nonneg _) ha hs hb

/-! ## AKraus part 3 (K2a): the slices of `V u` lie in the output space -/

open QAlgorithms.Papers.Independent.Gap48.P45 (outputSpace outputProjection)






end P45D


set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology
open Filter

attribute [local instance] Classical.propDecidable

namespace P45K

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P18
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond
  boundedConjugation)

/-! K3: second clause of `IsKrausRepresentation` (trace-norm convergence). Helpers copied
from scratch/probe/176d3efb_dual.lean and scratch/probe/12c0faa1.lean. -/

lemma hasSum_coord {I ι : Type} {f : ι → Hilbert I} {x : Hilbert I} (h : HasSum f x) (i : I) :
    HasSum (fun n => f n i) (x i) :=
  h.map (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i) (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i).continuous

lemma hasSum_basis {I : Type} (x : Hilbert I) :
    HasSum (fun j => x j • (lp.single 2 j (1 : ℂ) : Hilbert I)) x := by
  have := lp.hasSum_single (E := fun _ : I => ℂ) (p := 2) (by simp) x
  convert this using 2 with j <;> first | rfl | rw [← lp.single_smul, smul_eq_mul, mul_one]

lemma inner_single_right' {I : Type} (v : Hilbert I) (j : I) :
    inner ℂ v (lp.single 2 j (1 : ℂ) : Hilbert I) = star (v j) := by
  rw [lp.inner_single_right]
  simp [mul_comm]

lemma memℓp_two_iff' {T : Type} (f : T → ℂ) : Memℓp f 2 ↔ Summable (fun t => ‖f t‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simp

lemma hasSum_normSq {T : Type} (x : Hilbert T) : HasSum (fun t => ‖x t‖ ^ 2) (‖x‖ ^ 2) := by
  have := lp.hasSum_norm (by norm_num : 0 < (2:ℝ≥0∞).toReal) x
  simpa using this

def sliceV {T A : Type} (a : A) (x : Hilbert (T × A)) : Hilbert T :=
  ⟨fun t => x (t, a), by
    refine (memℓp_two_iff' (fun t => x (t, a))).mpr ?_
    exact (hasSum_normSq x).summable.comp_injective (i := fun t : T => ((t, a) : T × A))
      (fun u v h => by simpa using h)⟩

@[simp] lemma sliceV_apply {T A : Type} (a : A) (x : Hilbert (T × A)) (t : T) :
    sliceV a x t = x (t, a) := rfl

lemma fiber_normSq {T A : Type} (x : Hilbert (T × A)) :
    HasSum (fun a => ‖sliceV a x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := hasSum_normSq x
  have h' : HasSum ((fun p : T × A => ‖x p‖ ^ 2) ∘ Prod.swap) (‖x‖ ^ 2) :=
    (Equiv.prodComm A T).hasSum_iff.mpr h
  exact h'.prod_fiberwise (fun a => by simpa using hasSum_normSq (sliceV a x))

lemma norm_sliceV_le' {T A : Type} (a : A) (x : Hilbert (T × A)) : ‖sliceV a x‖ ≤ ‖x‖ := by
  have h := le_hasSum (fiber_normSq x) a (fun _ _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h






lemma norm_coord_le {T : Type} (x : Hilbert T) (t : T) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by norm_num) x t

/-! ## K3.1 balanced nuclear expansions -/


/-! ## K3.2 frame polarization -/




/-! ## K3.3 double-series swap -/




/-! ## K3.4 conjugating a nuclear expansion: `boundedConjugation` and `traceFirst` -/







/-! ## K3.5 expansions over a countable index, trace-class closure -/



lemma coeff_hasSum {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) (i j : T) :
    HasSum (fun n => e.left n i * star (e.right n j)) (X i j) := by
  rw [e.coefficients i j]
  refine (Summable.of_norm_bounded e.summable (fun n => ?_)).hasSum
  rw [norm_mul, norm_star]
  exact mul_le_mul (norm_coord_le _ _) (norm_coord_le _ _) (norm_nonneg _) (norm_nonneg _)







/-! ## K3.6 positive pieces `Mat w = Σ_n |w_n><w_n|` -/

lemma joint1 {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {a : α → ℝ} {s : ℝ}
    (ha : ∀ x, HasSum (fun y => g (x, y)) (a x)) (hs : HasSum a s) : HasSum g s := by
  have hsum : Summable g := (summable_prod_of_nonneg hg).mpr
    ⟨fun x => (ha x).summable, by simpa only [(ha _).tsum_eq] using hs.summable⟩
  have h2 := hsum.hasSum.prod_fiberwise ha
  rw [hs.unique h2]
  exact hsum.hasSum

lemma dsum_swap {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {a : α → ℝ} {b : β → ℝ}
    {s : ℝ} (ha : ∀ x, HasSum (fun y => g (x, y)) (a x)) (hs : HasSum a s)
    (hb : ∀ y, HasSum (fun x => g (x, y)) (b y)) : HasSum b s := by
  have h := joint1 g hg ha hs
  have h' : HasSum (g ∘ Prod.swap) s := (Equiv.prodComm β α).hasSum_iff.mpr h
  exact h'.prod_fiberwise hb

def Mat {T : Type} (w : ℕ → Hilbert T) : Matrix T T ℂ := fun i j => ∑' n, w n i * star (w n j)






/-! ## K3.7 polarization of a balanced expansion; the formula for `Psi X` -/





/-! ## K3.8 conjugation of a nuclear expansion (copied from scratch/probe/12c0faa1.lean) -/

lemma op_ext {I L : Type} {A B : Hilbert I →L[ℂ] Hilbert L}
    (h : operatorCoeff A = operatorCoeff B) : A = B := by
  ext1 x
  have hA := (hasSum_basis x).map A A.continuous
  have hB := (hasSum_basis x).map B B.continuous
  refine hA.unique ?_
  convert hB using 1
  funext j
  simp only [Function.comp, map_smul]
  congr 1
  ext i
  have := congrFun (congrFun h i) j
  simpa [operatorCoeff] using this

lemma bO_eq {I : Type} {X : Matrix I I ℂ} {T : Hilbert I →L[ℂ] Hilbert I}
    (h : operatorCoeff T = X) : boundedOperator X = T := by
  have hex : ∃ A : Hilbert I →L[ℂ] Hilbert I, operatorCoeff A = X := ⟨T, h⟩
  unfold boundedOperator
  rw [dif_pos hex]
  exact op_ext (hex.choose_spec.trans h.symm)

lemma operatorCoeff_apply {I L : Type} (A : Hilbert I →L[ℂ] Hilbert L) (i : L) (j : I) :
    operatorCoeff A i j = (A (lp.single 2 j 1)) i := by
  simp only [operatorCoeff]

def rk {I : Type} (u v : Hilbert I) : Hilbert I →L[ℂ] Hilbert I := (innerSL ℂ v).smulRight u

lemma rk_apply {I : Type} (u v x : Hilbert I) : rk u v x = inner ℂ v x • u := rfl

lemma norm_rk {I : Type} (u v : Hilbert I) : ‖rk u v‖ ≤ ‖u‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  rw [rk_apply, norm_smul]
  calc ‖inner ℂ v x‖ * ‖u‖ ≤ (‖v‖ * ‖x‖) * ‖u‖ := by
        gcongr; exact norm_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ * ‖x‖ := by ring

def nucOp {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) : Hilbert I →L[ℂ] Hilbert I :=
  ∑' n, rk (e.left n) (e.right n)

lemma nucOp_summable {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    Summable (fun n => rk (e.left n) (e.right n)) :=
  Summable.of_norm_bounded e.summable (fun n => norm_rk _ _)

lemma nucOp_hasSum {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (x : Hilbert I) :
    HasSum (fun n => inner ℂ (e.right n) x • e.left n) (nucOp e x) := by
  have := (nucOp_summable e).hasSum.map (ContinuousLinearMap.apply ℂ (Hilbert I) x)
    (ContinuousLinearMap.continuous _)
  exact this

lemma nucOp_coeff {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    operatorCoeff (nucOp e) = X := by
  funext i j
  rw [operatorCoeff_apply, e.coefficients i j]
  have h := hasSum_coord (nucOp_hasSum e (lp.single 2 j 1)) i
  refine (HasSum.tsum_eq ?_).symm
  convert h using 1
  funext n
  rw [inner_single_right']
  simp [mul_comm]

lemma bO_nuc {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    boundedOperator X = nucOp e := bO_eq (nucOp_coeff e)

lemma conj_hasSum {I L : Type} (B : Hilbert I →L[ℂ] Hilbert L) {X : Matrix I I ℂ}
    (e : NuclearExpansion X) (i j : L) :
    HasSum (fun n => B (e.left n) i * star (B (e.right n) j)) (conjugateCoeff B X i j) := by
  rw [conjugateCoeff, operatorCoeff_apply, bO_nuc e]
  rw [show (B.comp ((nucOp e).comp (ContinuousLinearMap.adjoint B))) (lp.single 2 j 1) =
    B (nucOp e (ContinuousLinearMap.adjoint B (lp.single 2 j 1))) from rfl]
  have h1 := (nucOp_hasSum e ((ContinuousLinearMap.adjoint B) (lp.single 2 j 1))).map B B.continuous
  have h2 := hasSum_coord h1 i
  convert h2 using 1
  funext n
  simp only [Function.comp, map_smul]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_single_right']
  simp [mul_comm]

/-! ## K3.9 the remainder `Psi X - Σ_{k∈F} A_k X A_k†` -/






/-! ## K3.10 the tails vanish -/


/-! ## K3 main: trace-norm convergence of the Kraus series -/


end P45K


noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology
open Filter

namespace P45A3

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass traceSize rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond
  boundedConjugation)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator IsKrausRepresentation)
open QAlgorithms.Papers.Independent.Gap48.P45 (operatorRank channelDual outputProjection)

/-- Part A3 (Kraus operators of the complement from a rank-one resolution of `P_out`). -/
def AKraus : Prop :=
  ∀ {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E), Complementary Phi Psi →
    ∀ (K : Type) [Countable K] (psi : K → Hilbert J),
      (∀ x, HasSum (fun k => ‖inner ℂ (psi k) x‖ ^ 2)
        (inner ℂ x (outputProjection Phi.val x)).re) →
      ∃ V : K → (Hilbert I →L[ℂ] Hilbert E), IsKrausRepresentation Psi.val V ∧
        ∀ k, operatorRank (V k) ≤
          operatorRank (channelDual Phi.val (boundedOperator (rankOne (psi k))))



end P45A3


/-! ## ALem2 (Lemma 2 of Shirokov, restricted form) -- session 6 -/

namespace P45L

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P18
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond
  boundedConjugation)
open QAlgorithms.Papers.Independent.Gap48.P45 (operatorRank channelDual outputSpace
  outputProjection rankMultiplicity restrictedDualNullity BoundIndex)
open P45D (sliceV sliceV_apply ampL ampL_apply ampV ampV_apply braL braL_apply braV braV_apply
  rk rk_apply hasSum_normSq)









section Stine

variable {I J E : Type} [Countable I] [Countable J] [Countable E]
  [Nonempty I] [Nonempty J] [Nonempty E]
  {Phi : Channel I J} {Psi : Channel I E} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
  (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
include hV




end Stine

















section Stine2

variable {I J E : Type} [Countable I] [Countable J] [Countable E]
  [Nonempty I] [Nonempty J] [Nonempty E]
  {Phi : Channel I J} {Psi : Channel I E} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
  (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
include hV



end Stine2



end P45L


set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace P45A

open QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (boundedOperator ReversibleOn IsKrausRepresentation)

/-! Split of ChildA (Kraus clause of Shirokov Thm 3) into three parts:
* `ARes`   reversibility core: a positive resolution `P_out = sum_i B_i` (quadratic-form sense),
           each `B_i` supported on the output space with `rank Phi^*(B_i) <= r`
           (`B_i = Phi(rho_bar)^{-1/2} pi_i Phi(rho_i) Phi(rho_bar)^{-1/2}`, Petz identity).
* `ALem2`  Lemma 2 (paper's restricted form, PDF p.10): such a `B` is a sum of at most
           `m_r = rankMultiplicity Phi r` rank-one terms, each with `rank Phi^*(|psi><psi|) <= r`.
* `AKraus` complement Kraus construction: a rank-one resolution of `P_out` gives Kraus operators
           `A_k = (<psi_k| (x) 1) V` of the complement with `rank A_k <= rank Phi^*(|psi_k><psi_k|)`.
-/

/-- Positivity in the form used by the platform's Lemma 2 statement. -/
def PosOp {J : Type} (B : Hilbert J →L[ℂ] Hilbert J) : Prop :=
  B.adjoint = B ∧ ∀ x, 0 ≤ (inner ℂ x (B x)).re

/-- Part A1 (reversibility core). -/
def ARes : Prop :=
  ∀ {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E), Complementary Phi Psi →
    ∀ (rho : L → State I) (r : ℕ), 0 < r → CompleteFamily (Set.range rho) →
    (∀ i, operatorRank (boundedOperator (rho i).coefficients) ≤ r) →
    ReversibleOn Phi.val (Set.range rho) →
    ∃ B : L → (Hilbert J →L[ℂ] Hilbert J),
      (∀ i, PosOp (B i)) ∧
      (∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
        (inner ℂ x (outputProjection Phi.val x)).re) ∧
      (∀ i, (outputProjection Phi.val).comp ((B i).comp (outputProjection Phi.val)) = B i) ∧
      ∀ i, operatorRank (channelDual Phi.val (B i)) ≤ r

/-- Part A2 (Lemma 2, restricted to the output support as in the paper). -/
def ALem2 : Prop :=
  ∀ {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (B : Hilbert J →L[ℂ] Hilbert J), PosOp B →
    (outputProjection Phi.val).comp (B.comp (outputProjection Phi.val)) = B →
    ∀ r : ℕ, operatorRank (channelDual Phi.val B) ≤ r →
    ∃ psi : BoundIndex (rankMultiplicity Phi.val r) → Hilbert J,
      (∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B x)).re) ∧
      ∀ j, operatorRank (channelDual Phi.val (boundedOperator (rankOne (psi j)))) ≤ r

/-- Part A3 (Kraus operators of the complement from a rank-one resolution of `P_out`). -/
def AKraus : Prop :=
  ∀ {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E), Complementary Phi Psi →
    ∀ (K : Type) [Countable K] (psi : K → Hilbert J),
      (∀ x, HasSum (fun k => ‖inner ℂ (psi k) x‖ ^ 2)
        (inner ℂ x (outputProjection Phi.val x)).re) →
      ∃ V : K → (Hilbert I →L[ℂ] Hilbert E), IsKrausRepresentation Psi.val V ∧
        ∀ k, operatorRank (V k) ≤
          operatorRank (channelDual Phi.val (boundedOperator (rankOne (psi k))))






end P45A

section ChildRoot

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)
open QAlgorithms.Papers.Independent.Gap48.P45 QAlgorithms.Papers.Independent.Dependency50.P33 QAlgorithms.Papers.Independent.Frontier18.P01 QAlgorithms.Papers.Independent.Frontier18.P18 in
theorem solution {I E : Type} [Countable I] [Countable E] [Nonempty I] [Nonempty E]
    (Psi : Channel I E) (r : ℕ) (bound : ℕ∞) (hr : 0 < r)
    (hK : HasBoundedRankKraus Psi.val r bound) :
    CountableSchmidtOutputs Psi.val r ∧ PartiallyEntanglementBreaking Psi.val r := by
  exact ⟨P45Aux.childB Psi r bound hr hK, P45Aux.childC Psi r hr (P45Aux.childB Psi r bound hr hK)⟩

end

end ChildRoot
