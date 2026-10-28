-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.dual_rank_rankOne_resolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:00:43.795422+00:00
-- url     : https://prove2.me/submissions/2c010cb2-c8b5-42b1-b6e5-098e78fd6296

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
noncomputable local instance (priority := 1100) scH_acg_1 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_1 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_1 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_1 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scC_acg_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommGroup (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_acm_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_mod_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Module ℂ (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_nacg_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : NormedAddCommGroup (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scH_am_1 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_1 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_1 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
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







/-- Expansion from coefficientwise HasSum. -/
def mkExp {I : Type} {X : Matrix I I ℂ} (u v : ℕ → Hilbert I)
    (hs : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hX : ∀ i j, HasSum (fun n => u n i * star (v n j)) (X i j)) : NuclearExpansion X where
  left := u
  right := v
  summable := hs
  coefficients := fun i j => (hX i j).tsum_eq.symm







/-! ## Part C: Cauchy-Schwarz on coordinates and the trace formula -/









/-! ## B1: a density is a countable sum of rank-one positives (via the CFC square root) -/





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




lemma fiber_normSq {T A : Type} (x : Hilbert (T × A)) :
    HasSum (fun a => ‖sliceV a x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := hasSum_normSq x
  have h' : HasSum ((fun p : T × A => ‖x p‖ ^ 2) ∘ Prod.swap) (‖x‖ ^ 2) :=
    (Equiv.prodComm A T).hasSum_iff.mpr h
  exact h'.prod_fiberwise (fun a => by simpa using hasSum_normSq (sliceV a x))


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



/-! ## B3: Schmidt rank of an amplified vector -/







/-! ## B4: entrywise Kraus convergence -/




/-! ## B5: a rank-one series converges in the bounded-operator trace norm -/








/-! ## B6: reindexing along an injection into ℕ, and the assembly -/








/-! ## Child C: countable Schmidt outputs give r-partial entanglement breaking -/



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




end P45Aux

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology

attribute [local instance] Classical.propDecidable

namespace P45D
noncomputable local instance (priority := 1100) scH_nacg_2 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_2 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_2 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_2 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_2 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_2 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ns_2 (X : Type) : NormedSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_2 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_am_2 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_2 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_2 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_2 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_snacg_2 (X Y : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_algR_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_algC_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℂ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_t2_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : T2Space (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_po_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : PartialOrder (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cstar_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : CStarAlgebra (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_sor_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_nsc_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cfcR_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_ncfcR_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_istR_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_smcR_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_star_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_tr_2 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsTopologicalRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_bcadd_2 (X : Type) : ContinuousAdd (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_btag_2 (X : Type) : IsTopologicalAddGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bccs_2 (X : Type) : ContinuousConstSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcs_2 (X : Type) : ContinuousSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bt2_2 (X : Type) : T2Space (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_badd_2 (X : Type) : Add (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bsmul_2 (X : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcladd_2 (X Y : Type) : Add (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsub_2 (X Y : Type) : Sub (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsmul_2 (X Y : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclmul_2 (X : Type) : Mul (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bclfun_2 (X Y : Type) : FunLike (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) (QAlgorithms.RealRegisters.Hilbert X) (QAlgorithms.RealRegisters.Hilbert Y) := inferInstance

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




lemma fiber_normSq {T A : Type} (x : Hilbert (T × A)) :
    HasSum (fun a => ‖sliceV a x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := hasSum_normSq x
  have h' : HasSum ((fun p : T × A => ‖x p‖ ^ 2) ∘ Prod.swap) (‖x‖ ^ 2) :=
    (Equiv.prodComm A T).hasSum_iff.mpr h
  exact h'.prod_fiberwise (fun a => by simpa using hasSum_normSq (sliceV a x))


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

/-- The unit-vector pure state has a density coefficient array. -/
lemma isDensity_rankOne {T : Type} (u : Hilbert T) (hu : ‖u‖ = 1) : IsDensity (rankOne u) := by
  have hsum : Summable (fun n : ℕ => ‖(if n = 0 then u else 0 : Hilbert T)‖ *
      ‖(if n = 0 then u else 0 : Hilbert T)‖) := by
    refine summable_of_ne_finset_zero (s := {0}) (fun n hn => ?_)
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  have hcoef : ∀ i j, rankOne u i j = ∑' n : ℕ, (if n = 0 then u else 0 : Hilbert T) i *
      star ((if n = 0 then u else 0 : Hilbert T) j) := by
    intro i j
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp [rankOne]
  refine ⟨⟨NuclearExpansion.mk _ _ hsum hcoef⟩, ?_, ?_, ?_⟩
  · intro s z
    have h : (∑ i ∈ s, ∑ j ∈ s, star (z i) * rankOne u i j * z j) =
        (∑ i ∈ s, star (z i) * u i) * star (∑ j ∈ s, star (z j) * u j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [star_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [rankOne, star_mul', star_star]
      ring
    rw [h]
    set w := ∑ i ∈ s, star (z i) * u i
    have : w * star w = ((Complex.normSq w : ℝ) : ℂ) := by
      rw [show star w = (starRingEnd ℂ) w from rfl, Complex.mul_conj]
    rw [this]
    exact ⟨Complex.ofReal_im _, by simpa using Complex.normSq_nonneg w⟩
  · have h := (hasSum_normSq u).summable
    refine h.congr (fun i => ?_)
    simp [rankOne, Complex.mul_conj', Complex.sq_norm]
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.sq_norm]
  · have h := (hasSum_normSq u).tsum_eq
    rw [hu, one_pow] at h
    rw [← h]
    refine tsum_congr (fun i => ?_)
    simp [rankOne, Complex.mul_conj', Complex.sq_norm]
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.sq_norm]

/-- The pure state of a unit vector. -/
def pureOf {T : Type} (u : Hilbert T) (hu : ‖u‖ = 1) : State T :=
  ⟨rankOne u, isDensity_rankOne u hu⟩

/-- Coordinates of `V u` as a basis series. -/
lemma V_coord {T U : Type} (V : Hilbert T →L[ℂ] Hilbert U) (u : Hilbert T) (p : U) :
    HasSum (fun i => u i * (V (lp.single 2 i (1 : ℂ))) p) ((V u) p) := by
  have h := hasSum_coord ((hasSum_basis u).map V V.continuous) p
  convert h using 1
  funext i
  simp [Function.comp, map_smul]

/-- Conjugating a rank-one array by `V`. -/
lemma bconj_rankOne {T U : Type} (V : Hilbert T →L[ℂ] Hilbert U) (u : Hilbert T) :
    boundedConjugation V (rankOne u) = rankOne (V u) := by
  funext p q
  simp only [boundedConjugation, rankOne]
  have hp := V_coord V u p
  have hq := V_coord V u q
  have hq' : HasSum (fun j => star (u j * (V (lp.single 2 j (1 : ℂ))) q)) (star ((V u) q)) :=
    hq.star
  have inner_eq : ∀ i, (∑' j, (V (lp.single 2 i (1 : ℂ))) p * (u i * star (u j)) *
      star ((V (lp.single 2 j (1 : ℂ))) q)) =
      (u i * (V (lp.single 2 i (1 : ℂ))) p) * star ((V u) q) := by
    intro i
    rw [← hq'.tsum_eq, ← tsum_mul_left]
    refine tsum_congr (fun j => ?_)
    simp only [star_mul']
    ring
  simp_rw [inner_eq]
  rw [tsum_mul_right, hp.tsum_eq]

/-- A complementary pair acts on a pure input through `rankOne (V u)`. -/
lemma phi_rankOne {I J E : Type} {Phi : Channel I J} {Psi : Channel I E}
    (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (u : Hilbert I) (hu : ‖u‖ = 1) :
    Phi.val (rankOne u) = traceSecond (rankOne (V u)) ∧
      Psi.val (rankOne u) = traceFirst (rankOne (V u)) := by
  obtain ⟨h1, h2⟩ := hV (pureOf u hu)
  simp only [pureOf] at h1 h2
  rw [bconj_rankOne] at h1 h2
  exact ⟨h1, h2⟩

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

/-- TARGET (next session): the Stinespring form of the dual of a complementary pair.
`channelDual Phi B = V† (B ⊗ 1) V`.  Plan: (1) `trTS`: HasSum over a of the diagonal of
`B ∘ boundedOperator (traceSecond (rankOne y))` to `⟪y, ampL B y⟫` (nuclear expansion of
traceSecond (rankOne y) with left = right = slices of y, reindexed to ℕ); (2) phi_rankOne for
non-unit u by scaling; (3) polarization `single j i 1 = (1/4) Σ_{c ∈ {1,I,-1,-I}} c • rankOne (e_j + c e_i)`
and Phi linear on trace class; (4) coefficients agree, conclude with op_ext / bO_eq. -/
def ADualStmt : Prop :=
  ∀ {I J E : Type} [Countable I] [Countable J] [Countable E] [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E)),
    (∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients)) →
    ∀ B : Hilbert J →L[ℂ] Hilbert J,
      QAlgorithms.Papers.Independent.Gap48.P45.channelDual Phi.val B =
        (ContinuousLinearMap.adjoint V.toContinuousLinearMap).comp
          ((ampL (E := E) B).comp V.toContinuousLinearMap)

/-! ## ADual part 1: row slices, the partial-trace operator and its trace pairing -/

def rowV {T A : Type} (t : T) (x : Hilbert (T × A)) : Hilbert A :=
  ⟨fun a => x (t, a), by
    refine (memℓp_two_iff' (fun a => x (t, a))).mpr ?_
    exact (hasSum_normSq x).summable.comp_injective (i := fun a : A => ((t, a) : T × A))
      (fun u v h => by simpa using h)⟩

@[simp] lemma rowV_apply {T A : Type} (t : T) (x : Hilbert (T × A)) (a : A) :
    rowV t x a = x (t, a) := rfl

/-- The outer-product array `|y><z|`. -/
def outerC {T : Type} (y z : Hilbert T) : Matrix T T ℂ := fun p q => y p * star (z q)

lemma rankOne_eq_outerC {T : Type} (u : Hilbert T) : rankOne u = outerC u u := rfl

lemma hasSum_traceSecond_outer {J E : Type} (y z : Hilbert (J × E)) (a b : J) :
    HasSum (fun r => y (a, r) * star (z (b, r))) (inner ℂ (rowV b z) (rowV a y)) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (rowV b z) (rowV a y)
  have e : (fun r => y (a, r) * star (z (b, r))) =
      (fun i => inner ℂ ((rowV b z) i) ((rowV a y) i)) := by
    funext r; simp [RCLike.inner_apply]
  rw [e]; exact h

lemma traceSecond_outer {J E : Type} (y z : Hilbert (J × E)) (a b : J) :
    traceSecond (outerC y z) a b = inner ℂ (rowV b z) (rowV a y) :=
  (hasSum_traceSecond_outer y z a b).tsum_eq

lemma summable_slice_mul {J E : Type} (y z : Hilbert (J × E)) :
    Summable (fun e : E => ‖sliceV e z‖ * ‖sliceV e y‖) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun e => ?_)
    (((fiber_normSq z).summable.add (fiber_normSq y).summable).div_const 2)
  nlinarith [sq_nonneg (‖sliceV e z‖ - ‖sliceV e y‖)]

lemma summable_outer_terms {J E : Type} (y z : Hilbert (J × E)) (x : Hilbert J) :
    Summable (fun e : E => inner ℂ (sliceV e z) x • sliceV e y) := by
  refine Summable.of_norm_bounded ((summable_slice_mul y z).mul_right ‖x‖) (fun e => ?_)
  rw [norm_smul]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (sliceV e z) x
  have h2 := norm_nonneg (sliceV e y)
  nlinarith

/-- The bounded operator `Σ_e |y_e><z_e|` realizing `traceSecond |y><z|`. -/
def outerOp {J E : Type} (y z : Hilbert (J × E)) : Hilbert J →L[ℂ] Hilbert J :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' e : E, inner ℂ (sliceV e z) x • sliceV e y
      map_add' := fun x x' => by
        simp only [inner_add_right, add_smul]
        exact (summable_outer_terms y z x).tsum_add (summable_outer_terms y z x')
      map_smul' := fun c x => by
        simp only [inner_smul_right, mul_smul, RingHom.id_apply]
        exact (summable_outer_terms y z x).tsum_const_smul c }
    (∑' e, ‖sliceV e z‖ * ‖sliceV e y‖) (fun x => by
      refine tsum_of_norm_bounded ((summable_slice_mul y z).hasSum.mul_right ‖x‖) (fun e => ?_)
      rw [norm_smul]
      have h1 := norm_inner_le_norm (𝕜 := ℂ) (sliceV e z) x
      have h2 := norm_nonneg (sliceV e y)
      nlinarith)

lemma outerOp_apply {J E : Type} (y z : Hilbert (J × E)) (x : Hilbert J) :
    outerOp y z x = ∑' e : E, inner ℂ (sliceV e z) x • sliceV e y := rfl

lemma outerOp_coeff {J E : Type} (y z : Hilbert (J × E)) :
    operatorCoeff (outerOp y z) = traceSecond (outerC y z) := by
  funext a b
  rw [operatorCoeff_apply, outerOp_apply]
  have h := hasSum_coord (summable_outer_terms y z (lp.single 2 b (1 : ℂ))).hasSum a
  rw [← h.tsum_eq]
  simp only [traceSecond, outerC]
  refine tsum_congr (fun e => ?_)
  rw [lp.coeFn_smul, Pi.smul_apply, inner_single_right', smul_eq_mul, sliceV_apply,
    sliceV_apply, mul_comm]

lemma bO_traceSecond_outer {J E : Type} (y z : Hilbert (J × E)) :
    boundedOperator (traceSecond (outerC y z)) = outerOp y z := bO_eq (outerOp_coeff y z)

/-- `Tr(B · traceSecond |y><z|) = ⟪z, (B ⊗ 1) y⟫`. -/
lemma tracePair_outer {J E : Type} (y z : Hilbert (J × E)) (B : Hilbert J →L[ℂ] Hilbert J) :
    QAlgorithms.Papers.Independent.Gap48.P45.boundedTracePair (traceSecond (outerC y z)) B =
      inner ℂ z (ampL (E := E) B y) := by
  unfold QAlgorithms.Papers.Independent.Gap48.P45.boundedTracePair
  rw [bO_traceSecond_outer, lp.inner_eq_tsum, (lp.summable_inner (𝕜 := ℂ) z (ampL (E := E) B y)).tsum_prod]
  refine tsum_congr (fun a => ?_)
  rw [operatorCoeff_apply, ContinuousLinearMap.comp_apply, outerOp_apply,
    B.map_tsum (summable_outer_terms y z _)]
  have hs : Summable (fun e : E => B (inner ℂ (sliceV e z) (lp.single 2 a (1 : ℂ)) • sliceV e y)) :=
    (summable_outer_terms y z _).map B B.continuous
  rw [← (hasSum_coord hs.hasSum a).tsum_eq]
  refine tsum_congr (fun e => ?_)
  rw [map_smul, lp.coeFn_smul, Pi.smul_apply, inner_single_right', smul_eq_mul, sliceV_apply,
    ampL_apply, ampV_apply, RCLike.inner_apply, mul_comm]
  rfl

/-! ## ADual part 2: polarization and the Stinespring form of the dual -/

lemma polar4 (p q s t : ℂ) :
    ∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) * ((p + Complex.I ^ k * q) * star (s + Complex.I ^ k * t)) =
      p * star t := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, star_add, star_mul', star_pow, hI]
  ring_nf
  have h4 : ∀ n : ℕ, Complex.I ^ (n + 4) = Complex.I ^ n := fun n => by
    rw [pow_add, Complex.I_pow_four, mul_one]
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have h9 : Complex.I ^ 9 = Complex.I := by rw [h4 5, h4 1, pow_one]
  have h6 : Complex.I ^ 6 = -1 := by rw [h4 2, Complex.I_sq]
  simp only [Complex.I_sq, Complex.I_pow_four, h3, h6, h9]
  ring_nf

lemma tc_finsum {T : Type} (N : ℕ) (l r : ℕ → Hilbert T) :
    IsTraceClass (fun a b => ∑ k ∈ Finset.range N, l k a * star (r k b)) := by
  refine ⟨⟨fun n => if n < N then l n else 0, fun n => if n < N then r n else 0, ?_, ?_⟩⟩
  · refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn => ?_)
    have : ¬ n < N := by simpa using hn
    simp [this]
  · intro a b
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      have : ¬ n < N := by simpa using hn
      simp [this])]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp [Finset.mem_range.mp hk]

lemma tc_combo {T : Type} (N : ℕ) (c : ℕ → ℂ) (u : ℕ → Hilbert T) :
    IsTraceClass (∑ k ∈ Finset.range N, c k • rankOne (u k)) := by
  have h := tc_finsum N (fun k => c k • u k) u
  have e : (∑ k ∈ Finset.range N, c k • rankOne (u k)) =
      (fun a b => ∑ k ∈ Finset.range N, (c k • u k) a * star (u k b)) := by
    funext a b
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [rankOne, mul_assoc]
  rw [e]; exact h

lemma tc_rankOne {T : Type} (u : Hilbert T) : IsTraceClass (rankOne u) := by
  simpa using tc_combo 1 (fun _ => (1 : ℂ)) (fun _ => u)

lemma phi_zero {I J : Type} (Phi : Channel I J) : Phi.val 0 = 0 := by
  have h0 : IsTraceClass (0 : Matrix I I ℂ) := by
    simpa using tc_combo (T := I) 0 (fun _ => 0) (fun _ => 0)
  have := Phi.2.2.2.1 0 0 h0
  simpa using this

lemma phi_finsum {I J : Type} (Phi : Channel I J) (c : ℕ → ℂ) (u : ℕ → Hilbert I) (N : ℕ) :
    Phi.val (∑ k ∈ Finset.range N, c k • rankOne (u k)) =
      ∑ k ∈ Finset.range N, c k • Phi.val (rankOne (u k)) := by
  induction N with
  | zero => simpa using phi_zero Phi
  | succ n ih =>
    have hS : IsTraceClass (c n • rankOne (u n)) := by
      simpa using tc_combo 1 (fun _ => c n) (fun _ => u n)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Phi.2.2.1 _ _ (tc_combo n c u) hS,
      Phi.2.2.2.1 _ _ (tc_rankOne (u n)), ih]

lemma rankOne_smul {T : Type} (c : ℂ) (u : Hilbert T) :
    rankOne (c • u) = (c * star c) • rankOne u := by
  funext a b; simp [rankOne]; ring

lemma traceSecond_smul {J E : Type} (c : ℂ) (X : Matrix (J × E) (J × E) ℂ) :
    traceSecond (c • X) = c • traceSecond X := by
  funext a b; simp [traceSecond, tsum_mul_left]

lemma phi_rankOne_all {I J E : Type} {Phi : Channel I J} {Psi : Channel I E}
    (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (u : Hilbert I) :
    Phi.val (rankOne u) = traceSecond (outerC (V u) (V u)) := by
  by_cases hu : u = 0
  · subst hu
    have h1 : rankOne (0 : Hilbert I) = 0 := by funext a b; simp [rankOne]
    have h2 : outerC (V 0) (V 0) = 0 := by funext a b; simp [outerC]
    rw [h1, h2, phi_zero]
    funext a b; simp [traceSecond]
  · have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    obtain ⟨t, w, hw, hu'⟩ : ∃ (t : ℂ) (w : Hilbert I), ‖w‖ = 1 ∧ u = t • w := by
      refine ⟨((‖u‖ : ℝ) : ℂ), (((‖u‖ : ℝ) : ℂ))⁻¹ • u, ?_, ?_⟩
      · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
        exact inv_mul_cancel₀ hn
      · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [hu', rankOne_smul, Phi.2.2.2.1 _ _ (tc_rankOne w), (phi_rankOne V hV w hw).1, map_smul,
      ← rankOne_eq_outerC, rankOne_smul, traceSecond_smul]

lemma single_polar {I : Type} (i j : I) :
    (Matrix.single j i (1 : ℂ) : Matrix I I ℂ) = ∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) •
      rankOne ((lp.single 2 j (1:ℂ) : Hilbert I) + Complex.I ^ k • lp.single 2 i (1:ℂ)) := by
  funext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, rankOne, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply,
    Pi.smul_apply]
  rw [polar4]
  simp only [lp.single_apply, Matrix.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

lemma traceSecond_polar {J E : Type} (y z : Hilbert (J × E)) :
    ∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) •
      traceSecond (outerC (y + Complex.I ^ k • z) (y + Complex.I ^ k • z)) =
      traceSecond (outerC y z) := by
  funext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hk : ∀ k ∈ Finset.range 4, HasSum (fun r => (Complex.I ^ k / 4) *
      ((y + Complex.I ^ k • z) (a, r) * star ((y + Complex.I ^ k • z) (b, r))))
      ((Complex.I ^ k / 4) *
        traceSecond (outerC (y + Complex.I ^ k • z) (y + Complex.I ^ k • z)) a b) := by
    intro k _
    rw [traceSecond_outer]
    exact (hasSum_traceSecond_outer _ _ a b).mul_left _
  have h := hasSum_sum hk
  have e : (fun r => ∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) *
      ((y + Complex.I ^ k • z) (a, r) * star ((y + Complex.I ^ k • z) (b, r)))) =
      fun r => y (a, r) * star (z (b, r)) := by
    funext r
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact polar4 _ _ _ _
  rw [e] at h
  rw [traceSecond_outer]
  exact h.unique (hasSum_traceSecond_outer y z a b)

lemma phi_single {I J E : Type} {Phi : Channel I J} {Psi : Channel I E}
    (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (i j : I) :
    Phi.val (Matrix.single j i (1 : ℂ)) =
      traceSecond (outerC (V (lp.single 2 j (1:ℂ))) (V (lp.single 2 i (1:ℂ)))) := by
  rw [single_polar, phi_finsum, ← traceSecond_polar]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [phi_rankOne_all V hV, map_add, map_smul]

/-- ADual: the dual of a channel with a Stinespring isometry is `V† (B ⊗ 1) V`. -/
theorem aDual : ADualStmt := by
  intro I J E _ _ _ _ _ _ Phi Psi V hV B
  unfold QAlgorithms.Papers.Independent.Gap48.P45.channelDual
  refine bO_eq ?_
  funext i j
  have hx : ∀ x : Hilbert I, x i = inner ℂ (lp.single 2 i (1:ℂ) : Hilbert I) x := by
    intro x; rw [lp.inner_single_left]; simp [RCLike.inner_apply]
  rw [operatorCoeff_apply]
  beta_reduce
  rw [phi_single V hV i j, tracePair_outer, hx, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-! ## AKraus part 1: bra operators `(<ψ| ⊗ 1)`, `A†A = Φ^*(|ψ><ψ|)` and the rank identity -/

open QAlgorithms.Papers.Independent.Gap48.P45 (operatorRank)

def rk {I : Type} (u v : Hilbert I) : Hilbert I →L[ℂ] Hilbert I := (innerSL ℂ v).smulRight u

lemma rk_apply {I : Type} (u v x : Hilbert I) : rk u v x = inner ℂ v x • u := rfl

lemma bO_rankOne {T : Type} (u : Hilbert T) : boundedOperator (rankOne u) = rk u u := by
  refine bO_eq ?_
  funext a b
  rw [operatorCoeff_apply, rk_apply, lp.coeFn_smul, Pi.smul_apply, inner_single_right', smul_eq_mul]
  simp [rankOne, mul_comm]

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

lemma bra_slice_hasSum {J E : Type} (psi : Hilbert J) (v y' : Hilbert (J × E)) (e : E) :
    HasSum (fun a : J => inner ℂ (v (a, e)) ((ampV (rk psi psi) y') (a, e)))
      (inner ℂ ((braV psi v) e) ((braV psi y') e)) := by
  have h := (lp.hasSum_inner (𝕜 := ℂ) (sliceV e v) psi).mul_left (inner ℂ psi (sliceV e y'))
  have e1 : (fun a : J => inner ℂ psi (sliceV e y') * inner ℂ ((sliceV e v) a) (psi a)) =
      (fun a : J => inner ℂ (v (a, e)) ((ampV (rk psi psi) y') (a, e))) := by
    funext a
    rw [ampV_apply, rk_apply, lp.coeFn_smul, Pi.smul_apply, sliceV_apply, smul_eq_mul,
      RCLike.inner_apply, RCLike.inner_apply]
    ring
  have e2 : inner ℂ psi (sliceV e y') * inner ℂ (sliceV e v) psi =
      inner ℂ ((braV psi v) e) ((braV psi y') e) := by
    rw [braV_apply, braV_apply, RCLike.inner_apply, inner_conj_symm, mul_comm]
  rw [e1, e2] at h
  exact h

lemma braL_adj_comp {J E : Type} (psi : Hilbert J) :
    (ContinuousLinearMap.adjoint (braL (E := E) psi)).comp (braL psi) = ampL (E := E) (rk psi psi) := by
  refine ContinuousLinearMap.ext (fun y' => ext_inner_left ℂ (fun v => ?_))
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, ampL_apply]
  have h := lp.hasSum_inner (𝕜 := ℂ) v (ampV (rk psi psi) y')
  have h' : HasSum ((fun p : J × E => inner ℂ (v p) ((ampV (rk psi psi) y') p)) ∘ Prod.swap)
      (inner ℂ v (ampV (rk psi psi) y')) := (Equiv.prodComm E J).hasSum_iff.mpr h
  have hf := h'.prod_fiberwise (fun e => bra_slice_hasSum psi v y' e)
  rw [lp.inner_eq_tsum]
  exact hf.tsum_eq

/-- The complement Kraus operator `A = (<ψ| ⊗ 1) V` has `A†A = Φ^*(|ψ><ψ|)`. -/
lemma kraus_dual {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    {Phi : Channel I J} {Psi : Channel I E} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (psi : Hilbert J) :
    (ContinuousLinearMap.adjoint ((braL (E := E) psi).comp V.toContinuousLinearMap)).comp
        ((braL psi).comp V.toContinuousLinearMap) =
      QAlgorithms.Papers.Independent.Gap48.P45.channelDual Phi.val (boundedOperator (rankOne psi)) := by
  rw [aDual Phi Psi V hV, bO_rankOne, ← braL_adj_comp, ContinuousLinearMap.adjoint_comp]
  ext1 x
  rfl

/-- `rank A = rank (A†A)` (first isomorphism theorem; `ker A = ker A†A`). -/
lemma rank_eq_adj_comp {T U : Type} (A : Hilbert T →L[ℂ] Hilbert U) :
    operatorRank A = operatorRank ((ContinuousLinearMap.adjoint A).comp A) := by
  unfold operatorRank
  have hker : LinearMap.ker A.toLinearMap =
      LinearMap.ker ((ContinuousLinearMap.adjoint A).comp A).toLinearMap := by
    ext x
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      have h2 : inner ℂ x ((ContinuousLinearMap.adjoint A) (A x)) = 0 := by
        rw [h, inner_zero_right]
      rw [ContinuousLinearMap.adjoint_inner_right] at h2
      exact inner_self_eq_zero.mp h2
  have e : LinearMap.range A.toLinearMap ≃ₗ[ℂ]
      LinearMap.range ((ContinuousLinearMap.adjoint A).comp A).toLinearMap :=
    (A.toLinearMap.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
      ((ContinuousLinearMap.adjoint A).comp A).toLinearMap.quotKerEquivRange
  rw [e.rank_eq]

/-- The rank clause of AKraus. -/
lemma kraus_rank {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    {Phi : Channel I J} {Psi : Channel I E} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (psi : Hilbert J) :
    operatorRank ((braL (E := E) psi).comp V.toContinuousLinearMap) =
      operatorRank (QAlgorithms.Papers.Independent.Gap48.P45.channelDual Phi.val
        (boundedOperator (rankOne psi))) := by
  rw [rank_eq_adj_comp, kraus_dual V hV psi]

/-! ## AKraus part 2 (generic): `Σ ‖A_k u‖² = ‖u‖²` gives strong convergence of `Σ A_k†A_k` to `1` -/

section KrausStrong

variable {K H F : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



end KrausStrong


/-! ## AKraus part 3 (K2a): the slices of `V u` lie in the output space -/

open QAlgorithms.Papers.Independent.Gap48.P45 (outputSpace outputProjection)




lemma outputProjection_fix {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (v : Hilbert J)
    (hv : v ∈ outputSpace Phi) : outputProjection Phi v = v := by
  letI : CompleteSpace (outputSpace Phi) :=
    (show IsClosed (outputSpace Phi : Set (Hilbert J)) from
      Submodule.isClosed_topologicalClosure _).completeSpace_coe
  unfold outputProjection
  exact Submodule.starProjection_eq_self_iff.mpr hv


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






lemma V_coord {T U : Type} (V : Hilbert T →L[ℂ] Hilbert U) (u : Hilbert T) (p : U) :
    HasSum (fun i => u i * (V (lp.single 2 i (1 : ℂ))) p) ((V u) p) := by
  have h := hasSum_coord ((hasSum_basis u).map V V.continuous) p
  convert h using 1
  funext i
  simp [Function.comp, map_smul]


/-! ## K3.1 balanced nuclear expansions -/


/-! ## K3.2 frame polarization -/

lemma polar4 (p q s t : ℂ) :
    ∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) * ((p + Complex.I ^ k * q) * star (s + Complex.I ^ k * t)) =
      p * star t := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, star_add, star_mul', star_pow, hI]
  ring_nf
  have h4 : ∀ n : ℕ, Complex.I ^ (n + 4) = Complex.I ^ n := fun n => by
    rw [pow_add, Complex.I_pow_four, mul_one]
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have h9 : Complex.I ^ 9 = Complex.I := by rw [h4 5, h4 1, pow_one]
  have h6 : Complex.I ^ 6 = -1 := by rw [h4 2, Complex.I_sq]
  have h5 : Complex.I ^ 5 = Complex.I := by rw [h4 1, pow_one]
  have h7 : Complex.I ^ 7 = -Complex.I := by rw [h4 3, h3]
  have h8 : Complex.I ^ 8 = 1 := by rw [h4 4, Complex.I_pow_four]
  simp only [Complex.I_sq, Complex.I_pow_four, h3, h5, h6, h7, h8, h9]
  ring_nf



/-! ## K3.3 double-series swap -/




/-! ## K3.4 conjugating a nuclear expansion: `boundedConjugation` and `traceFirst` -/







/-! ## K3.5 expansions over a countable index, trace-class closure -/










/-! ## K3.6 positive pieces `Mat w = Σ_n |w_n><w_n|` -/



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
noncomputable local instance (priority := 1100) scH_nacg_5 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_5 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_5 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_5 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_5 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_5 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_5 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scC_acg_5 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommGroup (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_acm_5 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_mod_5 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Module ℂ (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_top_5 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : TopologicalSpace (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_ring_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Ring (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scC_sr_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Semiring (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scH_am_5 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_5 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_5 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_5 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_acg_5 (X Y : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_acm_5 (X Y : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_am_5 (X Y : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_mod_5 (X Y : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_algR_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_algC_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℂ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_t2_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : T2Space (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_po_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : PartialOrder (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cstar_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : CStarAlgebra (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_sor_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_nsc_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cfcR_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_ncfcR_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_istR_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_smcR_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_star_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_tr_5 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsTopologicalRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_bcadd_5 (X : Type) : ContinuousAdd (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_btag_5 (X : Type) : IsTopologicalAddGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bccs_5 (X : Type) : ContinuousConstSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcs_5 (X : Type) : ContinuousSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bt2_5 (X : Type) : T2Space (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_badd_5 (X : Type) : Add (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bsmul_5 (X : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcladd_5 (X Y : Type) : Add (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsub_5 (X Y : Type) : Sub (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsmul_5 (X Y : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclmul_5 (X : Type) : Mul (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bclfun_5 (X Y : Type) : FunLike (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) (QAlgorithms.RealRegisters.Hilbert X) (QAlgorithms.RealRegisters.Hilbert Y) := inferInstance

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P18
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond
  boundedConjugation)
open QAlgorithms.Papers.Independent.Gap48.P45 (operatorRank channelDual outputSpace
  outputProjection rankMultiplicity restrictedDualNullity BoundIndex)
open P45D (sliceV sliceV_apply ampL ampL_apply ampV ampV_apply braL braL_apply braV braV_apply
  rk rk_apply hasSum_normSq)

/-- kernel inclusion bounds the rank (first isomorphism theorem). -/
lemma rank_le_of_ker {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] (A : X →ₗ[ℂ] Y) (C : X →ₗ[ℂ] Z)
    (h : LinearMap.ker A ≤ LinearMap.ker C) :
    Module.rank ℂ (LinearMap.range C) ≤ Module.rank ℂ (LinearMap.range A) := by
  rw [← (A.quotKerEquivRange).rank_eq, ← (C.quotKerEquivRange).rank_eq]
  refine LinearMap.rank_le_of_surjective
    ((LinearMap.ker A).liftQ (LinearMap.ker C).mkQ (by rwa [Submodule.ker_mkQ])) ?_
  intro q
  obtain ⟨x, rfl⟩ := (LinearMap.ker C).mkQ_surjective q
  exact ⟨(LinearMap.ker A).mkQ x, rfl⟩

lemma opRank_le_of_ker {I K L : Type} (A : Hilbert I →L[ℂ] Hilbert K)
    (C : Hilbert I →L[ℂ] Hilbert L) (h : ∀ x, A x = 0 → C x = 0) :
    operatorRank C ≤ operatorRank A := by
  unfold operatorRank
  exact OrderHomClass.mono Cardinal.toENat
    (rank_le_of_ker A.toLinearMap C.toLinearMap (fun x hx => h x hx))

/-- the square-root form `⟪y, S S y⟫ = ‖S y‖²`. -/
lemma form_sqrt {J : Type} {B S : Hilbert J →L[ℂ] Hilbert J} (hS : ContinuousLinearMap.adjoint S = S)
    (hSB : S * S = B) (y : Hilbert J) : inner ℂ y (B y) = ((‖S y‖ ^ 2 : ℝ) : ℂ) := by
  rw [← hSB, ContinuousLinearMap.mul_apply]
  conv_lhs => rw [← hS]
  rw [ContinuousLinearMap.adjoint_inner_right, hS, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma pos_ker {J : Type} {B S : Hilbert J →L[ℂ] Hilbert J} (hS : ContinuousLinearMap.adjoint S = S)
    (hSB : S * S = B) (y : Hilbert J) (h : (inner ℂ y (B y)).re = 0) : B y = 0 := by
  rw [form_sqrt hS hSB, Complex.ofReal_re] at h
  have h0 : S y = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  rw [← hSB, ContinuousLinearMap.mul_apply, h0, map_zero]

lemma ker_sqrt {J : Type} {B S : Hilbert J →L[ℂ] Hilbert J} (hS : ContinuousLinearMap.adjoint S = S)
    (hSB : S * S = B) (y : Hilbert J) (h : B y = 0) : S y = 0 := by
  have e := form_sqrt hS hSB y
  rw [h, inner_zero_right] at e
  have e2 : ‖S y‖ ^ 2 = 0 := by exact_mod_cast e.symm
  rw [← norm_eq_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2

lemma sqrt_exists' {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hA : A.IsPositive) : ∃ S : E →L[ℂ] E, IsSelfAdjoint S ∧ S * S = A :=
  ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).isSelfAdjoint,
    CFC.sqrt_mul_sqrt_self A ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hA)⟩

lemma sqrt_of_pos {J : Type} {B : Hilbert J →L[ℂ] Hilbert J}
    (h1 : ContinuousLinearMap.adjoint B = B) (h2 : ∀ x, 0 ≤ (inner ℂ x (B x)).re) :
    ∃ S : Hilbert J →L[ℂ] Hilbert J, ContinuousLinearMap.adjoint S = S ∧ S * S = B := by
  have hP : B.IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · change inner ℂ (B x) y = inner ℂ x (B y)
      rw [← ContinuousLinearMap.adjoint_inner_left, h1]
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm, RCLike.conj_re]
      exact h2 x
  obtain ⟨S, hS1, hS2⟩ := sqrt_exists' B hP
  exact ⟨S, hS1.adjoint_eq, hS2⟩

/-- the quadratic form of `B ⊗ 1` is the fiber sum. -/
lemma amp_form {J E : Type} (B : Hilbert J →L[ℂ] Hilbert J) (y : Hilbert (J × E)) :
    HasSum (fun e => inner ℂ (sliceV e y) (B (sliceV e y))) (inner ℂ y (ampL (E := E) B y)) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) y (ampL (E := E) B y)
  have h' : HasSum ((fun p : J × E => inner ℂ (y p) ((ampL (E := E) B y) p)) ∘ Prod.swap)
      (inner ℂ y (ampL (E := E) B y)) := (Equiv.prodComm E J).hasSum_iff.mpr h
  exact h'.prod_fiberwise (fun e => lp.hasSum_inner (𝕜 := ℂ) (sliceV e y) (B (sliceV e y)))

section Stine

variable {I J E : Type} [Countable I] [Countable J] [Countable E]
  [Nonempty I] [Nonempty J] [Nonempty E]
  {Phi : Channel I J} {Psi : Channel I E} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
  (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
include hV

lemma dual_ker {B S : Hilbert J →L[ℂ] Hilbert J} (hS : ContinuousLinearMap.adjoint S = S)
    (hSB : S * S = B) (hB : ∀ x, 0 ≤ (inner ℂ x (B x)).re)
    (x : Hilbert I) (hx : channelDual Phi.val B x = 0) (e : E) :
    B (sliceV e (V x)) = 0 := by
  have h0 : inner ℂ (V x) (ampL (E := E) B (V x)) = 0 := by
    have := congrArg (inner ℂ x) hx
    rw [P45D.aDual Phi Psi V hV B, inner_zero_right, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right] at this
    exact this
  have hs := (amp_form B (V x)).mapL Complex.reCLM
  rw [h0] at hs
  simp only [Complex.reCLM_apply, map_zero] at hs
  have h1 := (hasSum_zero_iff_of_nonneg (fun e => hB (sliceV e (V x)))).mp hs
  exact pos_ker hS hSB _ (congrFun h1 e)

lemma bra_ker {B S : Hilbert J →L[ℂ] Hilbert J} (hS : ContinuousLinearMap.adjoint S = S)
    (hSB : S * S = B) (hB : ∀ x, 0 ≤ (inner ℂ x (B x)).re)
    (psi : Hilbert J) (hpsi : ∀ z, B z = 0 → inner ℂ psi z = 0)
    (x : Hilbert I) (hx : channelDual Phi.val B x = 0) :
    ((braL (E := E) psi).comp V.toContinuousLinearMap) x = 0 := by
  refine lp.ext (funext fun e => ?_)
  show inner ℂ psi (sliceV e (V x)) = 0
  exact hpsi _ (dual_ker V hV hS hSB hB x hx e)

lemma rank_clause {B S : Hilbert J →L[ℂ] Hilbert J} (hS : ContinuousLinearMap.adjoint S = S)
    (hSB : S * S = B) (hB : ∀ x, 0 ≤ (inner ℂ x (B x)).re)
    (psi : Hilbert J) (hpsi : ∀ z, B z = 0 → inner ℂ psi z = 0) :
    operatorRank (channelDual Phi.val (boundedOperator (rankOne psi))) ≤
      operatorRank (channelDual Phi.val B) := by
  rw [← P45D.kraus_rank V hV psi]
  exact opRank_le_of_ker _ _ (fun x hx => bra_ker V hV hS hSB hB psi hpsi x hx)

end Stine

/-- a rank-one resolution of `B` is orthogonal to `ker B`. -/
lemma perp_ker {J M : Type} {B : Hilbert J →L[ℂ] Hilbert J} (psi : M → Hilbert J)
    (h : ∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B x)).re)
    (j : M) (z : Hilbert J) (hz : B z = 0) : inner ℂ (psi j) z = 0 := by
  have h0 := h z
  rw [hz, inner_zero_right, Complex.zero_re] at h0
  have h1 := (hasSum_zero_iff_of_nonneg (fun _ => sq_nonneg _)).mp h0
  have h2 : ‖inner ℂ (psi j) z‖ ^ 2 = 0 := congrFun h1 j
  rwa [sq_eq_zero_iff, norm_eq_zero] at h2

lemma ext_hasSum' {T N W α : Type} [Zero W] [AddCommMonoid α] [TopologicalSpace α] {g : T → N}
    (hg : Function.Injective g) (y : T → W) (F : W → α) (hF : F 0 = 0) {a : α}
    (h : HasSum (fun t => F (y t)) a) :
    HasSum (fun n => F (Function.extend g y 0 n)) a := by
  have hf : ∀ n ∉ Set.range g, F (Function.extend g y 0 n) = 0 := by
    intro n hn
    rw [Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hn)]
    exact hF
  refine (hg.hasSum_iff hf).mp ?_
  simpa [Function.comp_def, hg.extend_apply] using h

/-- infinite case: `ψ_j = S e_j`. -/
lemma decomp_top {J : Type} [Countable J] {B S : Hilbert J →L[ℂ] Hilbert J}
    (hS : ContinuousLinearMap.adjoint S = S) (hSB : S * S = B) :
    ∃ psi : BoundIndex ⊤ → Hilbert J,
      ∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B x)).re := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat J
  let g' : J → BoundIndex ⊤ := fun j => ⟨g j, ENat.natCast_lt_top _⟩
  have hg' : Function.Injective g' := fun a b h => hg (congrArg Subtype.val h)
  refine ⟨Function.extend g' (fun j => S (lp.single 2 j (1:ℂ))) 0, fun x => ?_⟩
  refine ext_hasSum' hg' _ (fun w => ‖inner ℂ w x‖ ^ 2) (by simp) ?_
  have e1 : ∀ j, ‖inner ℂ (S (lp.single 2 j (1:ℂ))) x‖ ^ 2 = ‖(S x) j‖ ^ 2 := by
    intro j
    conv_lhs => rw [← hS]
    rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left]
    simp
  simp only [e1]
  rw [form_sqrt hS hSB, Complex.ofReal_re]
  exact hasSum_normSq (S x)

lemma sa_inner {J : Type} {S : Hilbert J →L[ℂ] Hilbert J} (hS : ContinuousLinearMap.adjoint S = S)
    (y x : Hilbert J) : inner ℂ (S y) x = inner ℂ y (S x) := by
  rw [← ContinuousLinearMap.adjoint_inner_left, hS]

/-- finite case: `ψ_a = S b_a` for an orthonormal basis `b` of `range S`. -/
lemma decomp_fin {J : Type} {B S : Hilbert J →L[ℂ] Hilbert J}
    (hS : ContinuousLinearMap.adjoint S = S) (hSB : S * S = B) (n : ℕ)
    (hn : operatorRank B ≤ n) :
    ∃ psi : BoundIndex (n : ℕ∞) → Hilbert J,
      ∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B x)).re := by
  have hSr : operatorRank S ≤ n :=
    (opRank_le_of_ker B S (fun y hy => ker_sqrt hS hSB y hy)).trans hn
  have hWr : Module.rank ℂ (LinearMap.range S.toLinearMap) < Cardinal.aleph0 := by
    rw [← Cardinal.toENat_ne_top]
    exact ne_top_of_le_ne_top (ENat.coe_ne_top n) hSr
  haveI : FiniteDimensional ℂ (LinearMap.range S.toLinearMap) := Module.rank_lt_aleph0_iff.mp hWr
  have hk : Module.finrank ℂ (LinearMap.range S.toLinearMap) ≤ n := by
    have h1 : ((Module.finrank ℂ (LinearMap.range S.toLinearMap) : ℕ) : ℕ∞) ≤ n := by
      rw [← Cardinal.toENat_nat, Module.finrank_eq_rank]; exact hSr
    exact_mod_cast h1
  let b := stdOrthonormalBasis ℂ (LinearMap.range S.toLinearMap)
  let g : Fin (Module.finrank ℂ (LinearMap.range S.toLinearMap)) → BoundIndex (n : ℕ∞) :=
    fun a => ⟨a.1, Nat.cast_lt.mpr (lt_of_lt_of_le a.2 hk)⟩
  have hg : Function.Injective g := fun a c h => Fin.ext (congrArg Subtype.val h)
  refine ⟨Function.extend g (fun a => S (b a : Hilbert J)) 0, fun x => ?_⟩
  refine ext_hasSum' hg _ (fun w => ‖inner ℂ w x‖ ^ 2) (by simp) ?_
  let w : LinearMap.range S.toLinearMap := ⟨S x, LinearMap.mem_range_self _ x⟩
  have e1 : ∀ a, ‖inner ℂ (S (b a : Hilbert J)) x‖ ^ 2 = ‖inner ℂ (b a) w‖ ^ 2 := by
    intro a
    rw [sa_inner hS, Submodule.coe_inner]
  simp only [e1]
  rw [form_sqrt hS hSB, Complex.ofReal_re]
  have h2 := hasSum_fintype (fun a => ‖inner ℂ (b a) w‖ ^ 2)
  rw [b.sum_sq_norm_inner_right w] at h2
  exact h2

lemma ampL_add {J E : Type} (X Y : Hilbert J →L[ℂ] Hilbert J) :
    ampL (E := E) (X + Y) = ampL X + ampL Y := by
  ext y p; rfl

lemma ampL_smul {J E : Type} (c : ℂ) (X : Hilbert J →L[ℂ] Hilbert J) :
    ampL (E := E) (c • X) = c • ampL X := by
  ext y p; rfl

/-- `V† (X ⊗ 1) V` as a linear map in `X`. -/
def Dlin {I J E : Type} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E)) :
    (Hilbert J →L[ℂ] Hilbert J) →ₗ[ℂ] (Hilbert I →L[ℂ] Hilbert I) where
  toFun X := (ContinuousLinearMap.adjoint V.toContinuousLinearMap).comp
    ((ampL (E := E) X).comp V.toContinuousLinearMap)
  map_add' X Y := by
    rw [ampL_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c X := by
    rw [ampL_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, RingHom.id_apply]

lemma bra_slice_hasSum2 {J E : Type} (u w : Hilbert J) (v y' : Hilbert (J × E)) (e : E) :
    HasSum (fun a : J => inner ℂ (v (a, e)) ((ampV (rk u w) y') (a, e)))
      (inner ℂ ((braV u v) e) ((braV w y') e)) := by
  have h := (lp.hasSum_inner (𝕜 := ℂ) (sliceV e v) u).mul_left (inner ℂ w (sliceV e y'))
  have e1 : (fun a : J => inner ℂ w (sliceV e y') * inner ℂ ((sliceV e v) a) (u a)) =
      (fun a : J => inner ℂ (v (a, e)) ((ampV (rk u w) y') (a, e))) := by
    funext a
    rw [ampV_apply, rk_apply, lp.coeFn_smul, Pi.smul_apply, sliceV_apply, smul_eq_mul,
      RCLike.inner_apply, RCLike.inner_apply]
    ring
  have e2 : inner ℂ w (sliceV e y') * inner ℂ (sliceV e v) u =
      inner ℂ ((braV u v) e) ((braV w y') e) := by
    rw [braV_apply, braV_apply, RCLike.inner_apply, inner_conj_symm, mul_comm]
  rw [e1, e2] at h
  exact h

lemma braL_adj_comp2 {J E : Type} (u w : Hilbert J) :
    (ContinuousLinearMap.adjoint (braL (E := E) u)).comp (braL w) = ampL (E := E) (rk u w) := by
  refine ContinuousLinearMap.ext (fun y' => ext_inner_left ℂ (fun v => ?_))
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, ampL_apply]
  have h := lp.hasSum_inner (𝕜 := ℂ) v (ampV (rk u w) y')
  have h' : HasSum ((fun p : J × E => inner ℂ (v p) ((ampV (rk u w) y') p)) ∘ Prod.swap)
      (inner ℂ v (ampV (rk u w) y')) := (Equiv.prodComm E J).hasSum_iff.mpr h
  have hf := h'.prod_fiberwise (fun e => bra_slice_hasSum2 u w v y' e)
  rw [lp.inner_eq_tsum]
  exact hf.tsum_eq

/-- `Θ c = Σ c_ab |u_a><u_b|`. -/
def Theta {J ι : Type} [Fintype ι] (u : ι → Hilbert J) :
    Matrix ι ι ℂ →ₗ[ℂ] (Hilbert J →L[ℂ] Hilbert J) where
  toFun c := ∑ a, ∑ b, c a b • rk (u a) (u b)
  map_add' c d := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t c := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

lemma theta_apply {J ι : Type} [Fintype ι] (u : ι → Hilbert J) (c : Matrix ι ι ℂ) (x : Hilbert J) :
    Theta u c x = ∑ a, ∑ b, c a b • (inner ℂ (u b) x • u a) := by
  simp only [Theta, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, rk_apply]

lemma theta_inj {J ι : Type} [Fintype ι] (u : ι → Hilbert J) (hu : LinearIndependent ℂ u) :
    Function.Injective (Theta u) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have h1 : ∀ x a, ∑ b, c a b * inner ℂ (u b) x = 0 := by
    intro x
    have hx : ∑ a, (∑ b, c a b * inner ℂ (u b) x) • u a = 0 := by
      have := congrArg (fun T => T x) hc
      simp only [theta_apply, ContinuousLinearMap.zero_apply] at this
      refine Eq.trans ?_ this
      simp only [Finset.sum_smul, smul_smul]
    exact Fintype.linearIndependent_iff.mp hu _ hx
  ext a b
  have hv : ∀ x, inner ℂ (∑ b, (starRingEnd ℂ) (c a b) • u b) x = ∑ b, c a b * inner ℂ (u b) x := by
    intro x; simp only [sum_inner, inner_smul_left, Complex.conj_conj]
  have hv0 : ∑ b, (starRingEnd ℂ) (c a b) • u b = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hv, h1 _ a]
  have := Fintype.linearIndependent_iff.mp hu _ hv0 b
  simpa using this

lemma outProj_mem {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (v : Hilbert J) :
    outputProjection Phi v ∈ outputSpace Phi := by
  letI : CompleteSpace (outputSpace Phi) :=
    (show IsClosed (outputSpace Phi : Set (Hilbert J)) from
      Submodule.isClosed_topologicalClosure _).completeSpace_coe
  unfold outputProjection
  exact Submodule.starProjection_apply_mem _ v

lemma outProj_symm {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (v w : Hilbert J) :
    inner ℂ (outputProjection Phi v) w = inner ℂ v (outputProjection Phi w) := by
  letI : CompleteSpace (outputSpace Phi) :=
    (show IsClosed (outputSpace Phi : Set (Hilbert J)) from
      Submodule.isClosed_topologicalClosure _).completeSpace_coe
  unfold outputProjection
  exact Submodule.inner_starProjection_left_eq_right _ v w

lemma dlin_rk {I J E : Type} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E)) (v w : Hilbert J) :
    Dlin V (rk v w) = (ContinuousLinearMap.adjoint ((braL (E := E) v).comp V.toContinuousLinearMap)).comp
      ((braL w).comp V.toContinuousLinearMap) := by
  show (ContinuousLinearMap.adjoint V.toContinuousLinearMap).comp
    ((ampL (E := E) (rk v w)).comp V.toContinuousLinearMap) = _
  rw [← braL_adj_comp2, ContinuousLinearMap.adjoint_comp]
  ext1 x; rfl

section Stine2

variable {I J E : Type} [Countable I] [Countable J] [Countable E]
  [Nonempty I] [Nonempty J] [Nonempty E]
  {Phi : Channel I J} {Psi : Channel I E} (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
  (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
include hV

lemma dlin_eq (X : Hilbert J →L[ℂ] Hilbert J) : Dlin V X = channelDual Phi.val X :=
  (P45D.aDual Phi Psi V hV X).symm

/-- Lemma 2 counting: `n` independent vectors in `range B` force `n² ≤ m(Φ) + r²`. -/
lemma count {B : Hilbert J →L[ℂ] Hilbert J} (hBadj : ContinuousLinearMap.adjoint B = B)
    (hB : ∀ x, 0 ≤ (inner ℂ x (B x)).re)
    (hBsupp : (outputProjection Phi.val).comp (B.comp (outputProjection Phi.val)) = B)
    {ι : Type} [Fintype ι] (u : ι → Hilbert J) (hu : LinearIndependent ℂ u)
    (huB : ∀ a, ∃ w, B w = u a) (r : ℕ) (hr : operatorRank (channelDual Phi.val B) ≤ r) :
    ((Fintype.card ι : ℕ∞)) ^ 2 ≤ restrictedDualNullity Phi.val + (r : ℕ∞) ^ 2 := by
  obtain ⟨S, hS, hSB⟩ := sqrt_of_pos hBadj hB
  have hperp : ∀ a z, B z = 0 → inner ℂ (u a) z = 0 := by
    intro a z hz
    obtain ⟨w, hw⟩ := huB a
    rw [← hw, sa_inner hBadj, hz, inner_zero_right]
  have hout : ∀ a, outputProjection Phi.val (u a) = u a := by
    intro a
    obtain ⟨w, hw⟩ := huB a
    refine P45D.outputProjection_fix _ _ ?_
    rw [← hw, ← hBsupp]
    exact outProj_mem _ _
  let D0 := channelDual Phi.val B
  let K : Submodule ℂ (Hilbert I) := LinearMap.ker D0.toLinearMap
  haveI : CompleteSpace K := (D0.isClosed_ker).completeSpace_coe
  have hKr : Cardinal.toENat (Module.rank ℂ Kᗮ) ≤ r := by
    rw [← (Submodule.quotientEquivOfIsCompl K Kᗮ (Submodule.isCompl_orthogonal K)).rank_eq,
      (LinearMap.quotKerEquivRange D0.toLinearMap).rank_eq]
    exact hr
  haveI : FiniteDimensional ℂ Kᗮ := by
    refine Module.rank_lt_aleph0_iff.mp ?_
    rw [← Cardinal.toENat_ne_top]
    exact ne_top_of_le_ne_top (ENat.coe_ne_top r) hKr
  have hfK : (Module.finrank ℂ Kᗮ : ℕ∞) ≤ r := by
    rw [← Cardinal.toENat_nat, Module.finrank_eq_rank]; exact hKr
  let Z : Submodule ℂ (Hilbert I →L[ℂ] Hilbert I) :=
    { carrier := {Y | (∀ k ∈ K, Y k = 0) ∧ ∀ x, Y x ∈ Kᗮ}
      add_mem' := by
        rintro Y Y' ⟨h1, h2⟩ ⟨h1', h2'⟩
        exact ⟨fun k hk => by rw [ContinuousLinearMap.add_apply, h1 k hk, h1' k hk, add_zero],
          fun x => Kᗮ.add_mem (h2 x) (h2' x)⟩
      zero_mem' := ⟨fun k _ => rfl, fun x => Kᗮ.zero_mem⟩
      smul_mem' := by
        rintro c Y ⟨h1, h2⟩
        exact ⟨fun k hk => by rw [ContinuousLinearMap.smul_apply, h1 k hk, smul_zero],
          fun x => Kᗮ.smul_mem c (h2 x)⟩ }
  have hZ : ∀ Y, Y ∈ Z → (∀ k ∈ K, Y k = 0) ∧ ∀ x, Y x ∈ Kᗮ := fun Y h => h
  have hZi : ∀ Y : Hilbert I →L[ℂ] Hilbert I, (∀ k ∈ K, Y k = 0) → (∀ x, Y x ∈ Kᗮ) → Y ∈ Z :=
    fun Y h1 h2 => show _ ∧ _ from ⟨h1, h2⟩
  have hrkZ : ∀ a b, Dlin V (rk (u a) (u b)) ∈ Z := by
    intro a b
    rw [dlin_rk]
    refine hZi _ (fun k hk => ?_) (fun x => ?_)
    · rw [ContinuousLinearMap.comp_apply,
        bra_ker V hV hS hSB hB (u b) (hperp b) k (LinearMap.mem_ker.mp hk), map_zero]
    · rw [Submodule.mem_orthogonal]
      intro k hk
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        bra_ker V hV hS hSB hB (u a) (hperp a) k (LinearMap.mem_ker.mp hk), inner_zero_left]
  have hmem : ∀ c, (Dlin V ∘ₗ Theta u) c ∈ Z := by
    intro c
    show Dlin V (∑ a, ∑ b, c a b • rk (u a) (u b)) ∈ Z
    rw [map_sum]
    refine Z.sum_mem (fun a _ => ?_)
    rw [map_sum]
    refine Z.sum_mem (fun b _ => ?_)
    rw [map_smul]
    exact Z.smul_mem _ (hrkZ a b)
  let Γ : Matrix ι ι ℂ →ₗ[ℂ] Z := (Dlin V ∘ₗ Theta u).codRestrict Z hmem
  let ρ : Z →ₗ[ℂ] (Kᗮ →ₗ[ℂ] Kᗮ) :=
    { toFun := fun Y => ((Y.1.toLinearMap).domRestrict Kᗮ).codRestrict Kᗮ (fun w => (hZ _ Y.2).2 w)
      map_add' := fun Y Y' => LinearMap.ext fun w => Subtype.ext rfl
      map_smul' := fun c Y => LinearMap.ext fun w => Subtype.ext rfl }
  have hρ : ∀ Y, ρ Y = 0 → Y = 0 := by
    intro Y hY
    apply Subtype.ext
    ext1 x
    have hx : x ∈ K ⊔ Kᗮ := by
      rw [(Submodule.isCompl_orthogonal K).sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    have h1 : (Y : Hilbert I →L[ℂ] Hilbert I) w = 0 := by
      have := congrArg (fun f => ((f ⟨w, hw⟩ : Kᗮ) : Hilbert I)) hY
      exact this
    rw [map_add, (hZ _ Y.2).1 k hk, h1, add_zero]
    rfl
  let Ω := ρ ∘ₗ Γ
  have hrn := LinearMap.finrank_range_add_finrank_ker Ω
  have hmat : Module.finrank ℂ (Matrix ι ι ℂ) = Fintype.card ι * Fintype.card ι := by
    rw [Module.finrank_matrix, Module.finrank_self, mul_one]
  have hrange : Module.finrank ℂ (LinearMap.range Ω) ≤ Module.finrank ℂ Kᗮ * Module.finrank ℂ Kᗮ :=
    (Submodule.finrank_le _).trans (Module.finrank_linearMap ℂ ℂ Kᗮ Kᗮ).le
  have hsupp : ∀ c, (outputProjection Phi.val).comp ((Theta u c).comp (outputProjection Phi.val)) =
      Theta u c := by
    intro c
    ext1 x
    simp only [ContinuousLinearMap.comp_apply, theta_apply, map_sum, map_smul, hout]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [← outProj_symm, hout]
  let S0 : Set (Hilbert J →L[ℂ] Hilbert J) := {B' |
      (outputProjection Phi.val).comp (B'.comp (outputProjection Phi.val)) = B' ∧
        channelDual Phi.val B' = 0}
  have hkerS0 : ∀ c ∈ LinearMap.ker Ω, Theta u c ∈ Submodule.span ℂ S0 := by
    intro c hc
    refine Submodule.subset_span (show _ ∧ _ from ⟨hsupp c, ?_⟩)
    have h1 : Γ c = 0 := hρ _ (LinearMap.mem_ker.mp hc)
    have h2 : Dlin V (Theta u c) = 0 := congrArg Subtype.val h1
    rw [← dlin_eq V hV]; exact h2
  let θ' : LinearMap.ker Ω →ₗ[ℂ] Submodule.span ℂ S0 :=
    ((Theta u).domRestrict (LinearMap.ker Ω)).codRestrict _ (fun c => hkerS0 c.1 c.2)
  have hθ' : Function.Injective θ' := by
    intro c d h
    exact Subtype.ext (theta_inj u hu (congrArg Subtype.val h))
  have hker : (Module.finrank ℂ (LinearMap.ker Ω) : ℕ∞) ≤ restrictedDualNullity Phi.val := by
    rw [← Cardinal.toENat_nat, Module.finrank_eq_rank]
    exact OrderHomClass.mono Cardinal.toENat (LinearMap.rank_le_of_injective θ' hθ')
  have hsq : ((Fintype.card ι : ℕ∞)) ^ 2 =
      (Module.finrank ℂ (LinearMap.range Ω) : ℕ∞) + (Module.finrank ℂ (LinearMap.ker Ω) : ℕ∞) := by
    rw [sq]; exact_mod_cast (hrn.trans hmat).symm
  rw [hsq, add_comm (restrictedDualNullity Phi.val)]
  refine add_le_add ?_ hker
  calc (Module.finrank ℂ (LinearMap.range Ω) : ℕ∞)
      ≤ ((Module.finrank ℂ Kᗮ * Module.finrank ℂ Kᗮ : ℕ) : ℕ∞) := by exact_mod_cast hrange
    _ = (Module.finrank ℂ Kᗮ : ℕ∞) * (Module.finrank ℂ Kᗮ : ℕ∞) := by push_cast; rfl
    _ ≤ (r : ℕ∞) * r := mul_le_mul' hfK hfK
    _ = (r : ℕ∞) ^ 2 := (sq _).symm

end Stine2

/-- ALem2 with the complementary pair (needed for the Stinespring form of the dual). -/
def ALem2' : Prop :=
  ∀ {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E), Complementary Phi Psi →
    ∀ (B : Hilbert J →L[ℂ] Hilbert J),
    (ContinuousLinearMap.adjoint B = B ∧ ∀ x, 0 ≤ (inner ℂ x (B x)).re) →
    (outputProjection Phi.val).comp (B.comp (outputProjection Phi.val)) = B →
    ∀ r : ℕ, operatorRank (channelDual Phi.val B) ≤ r →
    ∃ psi : BoundIndex (rankMultiplicity Phi.val r) → Hilbert J,
      (∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B x)).re) ∧
      ∀ j, operatorRank (channelDual Phi.val (boundedOperator (rankOne (psi j)))) ≤ r

theorem aLem2 : ALem2' := by
  intro I J E _ _ _ _ _ _ Phi Psi hComp B hBpos hBsupp r hr
  obtain ⟨V, hV⟩ := hComp
  obtain ⟨S, hS, hSB⟩ := sqrt_of_pos hBpos.1 hBpos.2
  have fin : ∀ {m : ℕ∞} (psi : BoundIndex m → Hilbert J),
      (∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B x)).re) →
      ∀ j, operatorRank (channelDual Phi.val (boundedOperator (rankOne (psi j)))) ≤ r :=
    fun psi h j =>
      (rank_clause V hV hS hSB hBpos.2 (psi j) (fun z hz => perp_ker psi h j z hz)).trans hr
  have hrange : LinearMap.range B.toLinearMap ≤ outputSpace Phi.val := by
    rintro _ ⟨w, rfl⟩
    show B w ∈ outputSpace Phi.val
    rw [← hBsupp]; exact outProj_mem _ _
  have b1 : operatorRank B ≤ Cardinal.toENat (Module.rank ℂ (outputSpace Phi.val)) :=
    OrderHomClass.mono Cardinal.toENat (Submodule.rank_mono hrange)
  have b2 : operatorRank B ≤ restrictedDualNullity Phi.val + (r : ℕ∞) ^ 2 := by
    by_contra hlt
    push_neg at hlt
    have hfin : restrictedDualNullity Phi.val + (r : ℕ∞) ^ 2 ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← ht] at hlt
    have h1 : ((t + 1 : ℕ) : ℕ∞) ≤ operatorRank B := by
      exact_mod_cast Order.add_one_le_of_lt hlt
    have h2 : ((t + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ (LinearMap.range B.toLinearMap) :=
      Cardinal.natCast_le_toENat.mp h1
    obtain ⟨s, hs, hli⟩ := le_rank_iff_exists_linearIndependent_finset.mp h2
    have hli' : LinearIndependent ℂ
        (fun a : s => ((a : LinearMap.range B.toLinearMap) : Hilbert J)) :=
      hli.map' (LinearMap.range B.toLinearMap).subtype (Submodule.ker_subtype _)
    have hc := count V hV hBpos.1 hBpos.2 hBsupp _ hli'
      (fun a => LinearMap.mem_range.mp (a : LinearMap.range B.toLinearMap).2) r hr
    rw [← ht, Fintype.card_coe, hs] at hc
    have h3 : (t + 1) ^ 2 ≤ t := by exact_mod_cast hc
    nlinarith
  by_cases hm : rankMultiplicity Phi.val r = ⊤
  · rw [hm]
    obtain ⟨psi, hpsi⟩ := decomp_top (J := J) hS hSB
    exact ⟨psi, hpsi, fin psi hpsi⟩
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hm
    rw [← hn]
    have hBn : operatorRank B ≤ n := by
      rw [hn]; exact le_min b2 b1
    obtain ⟨psi, hpsi⟩ := decomp_fin hS hSB n hBn
    exact ⟨psi, hpsi, fin psi hpsi⟩

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
theorem solution {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (B : Hilbert J →L[ℂ] Hilbert J)
    (hB : ContinuousLinearMap.adjoint B = B ∧ ∀ x, 0 ≤ (inner ℂ x (B x)).re)
    (hsupp : (outputProjection Phi.val).comp (B.comp (outputProjection Phi.val)) = B)
    (r : ℕ) (hr : operatorRank (channelDual Phi.val B) ≤ r) :
    ∃ psi : BoundIndex (rankMultiplicity Phi.val r) → Hilbert J,
      (∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B x)).re) ∧
      ∀ j, operatorRank (channelDual Phi.val (boundedOperator (rankOne (psi j)))) ≤ r := by
  exact P45L.aLem2 Phi Psi hComp B hB hsupp r hr

end

end ChildRoot
