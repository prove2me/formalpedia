-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.rankOne_kraus_orthogonal_rows_series
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:51:03.376132+00:00
-- url     : https://prove2.me/submissions/2a73aaff-7fa4-4729-920d-3ad05c41a15e

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
noncomputable local instance (priority := 1100) scH_am_1 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_1 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_1 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_1 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_acm_1 (X Y : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_top_1 (X Y : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_snacg_1 (X Y : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
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


lemma ts_le {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) :
    traceSize X ≤ ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖) := iInf_le _ e





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












/-! ## B3: Schmidt rank of an amplified vector -/







/-! ## B4: entrywise Kraus convergence -/

lemma coord_le {T : Type} (x : Hilbert T) (t : T) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by norm_num) x t



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


lemma expAdd_tsum {T : Type} {X Y : Matrix T T ℂ} (e1 : NuclearExpansion X)
    (e2 : NuclearExpansion Y) :
    ∑' m, ‖(expAdd e1 e2).left m‖ * ‖(expAdd e1 e2).right m‖ =
      (∑' n, ‖e1.left n‖ * ‖e1.right n‖) + ∑' n, ‖e2.left n‖ * ‖e2.right n‖ := by
  change ∑' m, ‖ileave e1.left e2.left m‖ * ‖ileave e1.right e2.right m‖ = _
  exact (HasSum.even_add_odd (f := fun m => ‖ileave e1.left e2.left m‖ *
        ‖ileave e1.right e2.right m‖)
      (by simpa only [ileave_even] using e1.summable.hasSum)
      (by simpa only [ileave_odd] using e2.summable.hasSum)).tsum_eq

end P45Aux

end

section N2W2

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter

attribute [local instance] Classical.propDecidable

namespace P45G
noncomputable local instance (priority := 1100) scH_nacg_2 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_2 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_2 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_2 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_2 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_2 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scC_acm_2 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_2 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_acm_2 (X Y : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
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

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion IsTraceClass traceSize rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Gap48.P45 (coefficientTraceHasSum)
open P45Aux

variable {T : Type}

lemma tc_zero : IsTraceClass (0 : Matrix T T ℂ) :=
  ⟨mkExp (fun _ => 0) (fun _ => 0) (by simp) (fun i j => by simpa using hasSum_zero)⟩

lemma tc_add {X Y : Matrix T T ℂ} (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    IsTraceClass (X + Y) := by
  obtain ⟨e1⟩ := hX; obtain ⟨e2⟩ := hY; exact ⟨expAdd e1 e2⟩

lemma tc_neg {X : Matrix T T ℂ} (hX : IsTraceClass X) : IsTraceClass (-X) := by
  obtain ⟨e⟩ := hX; exact ⟨expNeg e⟩

lemma tc_sub {X Y : Matrix T T ℂ} (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    IsTraceClass (X - Y) := by
  rw [sub_eq_add_neg]; exact tc_add hX (tc_neg hY)

lemma tc_sum {ι : Type} (s : Finset ι) (f : ι → Matrix T T ℂ) (hf : ∀ i, IsTraceClass (f i)) :
    IsTraceClass (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (tc_zero : IsTraceClass (0 : Matrix T T ℂ))
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact tc_add (hf a) ih

lemma ts_zero : traceSize (0 : Matrix T T ℂ) = 0 := by
  refine le_antisymm ((ts_le (mkExp (fun _ => (0 : Hilbert T)) (fun _ => 0) (by simp)
    (fun i j => by simpa using hasSum_zero))).trans ?_) zero_le
  show ENNReal.ofReal (∑' n : ℕ, ‖(0 : Hilbert T)‖ * ‖(0 : Hilbert T)‖) ≤ 0
  simp

lemma ts_add {X Y : Matrix T T ℂ} (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    traceSize (X + Y) ≤ traceSize X + traceSize Y := by
  haveI := hX; haveI := hY
  exact ENNReal.le_iInf_add_iInf (fun e1 e2 => (ts_le (expAdd e1 e2)).trans (by
    rw [expAdd_tsum, ENNReal.ofReal_add (tsum_nonneg fun _ => by positivity)
      (tsum_nonneg fun _ => by positivity)]))

lemma ts_neg_le (X : Matrix T T ℂ) : traceSize (-X) ≤ traceSize X :=
  le_iInf (fun e => (ts_le (expNeg e)).trans_eq (by rw [expNeg_tsum]))

lemma ts_sum_le {ι : Type} (s : Finset ι) (f : ι → Matrix T T ℂ) (hf : ∀ i, IsTraceClass (f i)) :
    traceSize (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceSize (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ts_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ts_add (hf a) (tc_sum s f hf)).trans (add_le_add le_rfl ih)


lemma bO_sub {X Y : Matrix T T ℂ} (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    boundedOperator (X - Y) = boundedOperator X - boundedOperator Y :=
  bO_eq (by rw [coeff_sub, coeff_bO hX, coeff_bO hY])

lemma bO_sum {ι : Type} (s : Finset ι) (f : ι → Matrix T T ℂ) (hf : ∀ i, IsTraceClass (f i)) :
    boundedOperator (∑ i ∈ s, f i) = ∑ i ∈ s, boundedOperator (f i) :=
  bO_eq (by rw [coeff_sum]; exact Finset.sum_congr rfl (fun i _ => coeff_bO (hf i)))

lemma p39_of {X : Matrix T T ℂ} (e : NuclearExpansion X) :
    QAlgorithms.Papers.Independent.Dependency50.P39.NuclearExpansion (boundedOperator X)
      e.left e.right := by
  rw [bO_nuc e]; exact p39_ne e.left e.right e.summable

lemma p39_tc {X : Matrix T T ℂ} (hX : IsTraceClass X) :
    QAlgorithms.Papers.Independent.Dependency50.P39.IsTraceClass (boundedOperator X) := by
  obtain ⟨e⟩ := hX; exact ⟨e.left, e.right, p39_of e⟩

lemma ntn_le_ts {X : Matrix T T ℂ} (hX : IsTraceClass X) :
    QAlgorithms.Papers.Independent.Dependency50.P39.nuclearTraceNorm (boundedOperator X) ≤
      (traceSize X).toReal := by
  obtain ⟨e0⟩ := hX
  have hfin : traceSize X ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (ts_le e0)
  have h : ENNReal.ofReal (QAlgorithms.Papers.Independent.Dependency50.P39.nuclearTraceNorm
      (boundedOperator X)) ≤ traceSize X :=
    le_iInf (fun e => ENNReal.ofReal_le_ofReal (ntn_le (p39_of e)))
  have := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_ofReal (ntn_nonneg _)] at this

/-- Grouping: a trace-norm series over `L × M` whose fibres converge in trace norm
regroups into a coefficient trace series over `L`. -/
theorem group_series {L M : Type} (Y : Matrix T T ℂ) (hY : IsTraceClass Y)
    (a : L × M → Matrix T T ℂ) (ha : ∀ p, IsTraceClass (a p))
    (f : L → Matrix T T ℂ) (hf : ∀ i, IsTraceClass (f i))
    (hfib : ∀ i, Tendsto (fun J : Finset M => traceSize (f i - ∑ j ∈ J, a (i, j))) atTop (𝓝 0))
    (htot : Tendsto (fun F : Finset (L × M) => traceSize (Y - ∑ p ∈ F, a p)) atTop (𝓝 0)) :
    coefficientTraceHasSum f Y := by
  have hG : Tendsto (fun G : Finset L => traceSize (Y - ∑ i ∈ G, f i)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨F0, hF0⟩ := Filter.eventually_atTop.mp
      ((ENNReal.tendsto_nhds_zero.mp htot) (ε / 2) hε2)
    rw [Filter.eventually_atTop]
    refine ⟨F0.image Prod.fst, fun G hG => ?_⟩
    have hbound : ∀ J : Finset M, F0.image Prod.snd ≤ J →
        traceSize (Y - ∑ i ∈ G, f i) ≤
          ε / 2 + ∑ i ∈ G, traceSize (f i - ∑ j ∈ J, a (i, j)) := by
      intro J hJ
      have hsub : F0 ≤ G ×ˢ J := fun p hp =>
        Finset.mem_product.mpr ⟨hG (Finset.mem_image_of_mem _ hp),
          hJ (Finset.mem_image_of_mem _ hp)⟩
      have hdecomp : Y - ∑ i ∈ G, f i = (Y - ∑ p ∈ G ×ˢ J, a p) +
          ∑ i ∈ G, -(f i - ∑ j ∈ J, a (i, j)) := by
        rw [Finset.sum_product]
        simp only [neg_sub, Finset.sum_sub_distrib]
        abel
      have htcF : IsTraceClass (Y - ∑ p ∈ G ×ˢ J, a p) := tc_sub hY (tc_sum _ a ha)
      have htci : ∀ i, IsTraceClass (-(f i - ∑ j ∈ J, a (i, j))) := fun i =>
        tc_neg (tc_sub (hf i) (tc_sum _ _ (fun j => ha (i, j))))
      rw [hdecomp]
      refine (ts_add htcF (tc_sum _ _ htci)).trans (add_le_add (hF0 _ hsub) ?_)
      exact (ts_sum_le _ _ htci).trans (Finset.sum_le_sum (fun i _ => ts_neg_le _))
    have hlim : Tendsto (fun J : Finset M =>
        ε / 2 + ∑ i ∈ G, traceSize (f i - ∑ j ∈ J, a (i, j))) atTop (𝓝 (ε / 2 + 0)) := by
      refine tendsto_const_nhds.add ?_
      simpa using tendsto_finset_sum G (fun i _ => hfib i)
    rw [add_zero] at hlim
    have h1 : traceSize (Y - ∑ i ∈ G, f i) ≤ ε / 2 :=
      ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨F0.image Prod.snd, hbound⟩)
    exact h1.trans ENNReal.half_le_self
  refine ⟨hY, hf, p39_tc hY, fun s => ?_, fun s => ?_, ?_⟩
  · rw [← bO_sum s f hf]; exact p39_tc (tc_sum s f hf)
  · rw [← bO_sum s f hf, ← bO_sub (tc_sum s f hf) hY]
    exact p39_tc (tc_sub (tc_sum s f hf) hY)
  · have hD : ∀ s : Finset L, (∑ i ∈ s, boundedOperator (f i)) - boundedOperator Y =
        boundedOperator (-(Y - ∑ i ∈ s, f i)) := fun s => by
      rw [neg_sub, bO_sub (tc_sum s f hf) hY, bO_sum s f hf]
    simp_rw [hD]
    have hup : Tendsto (fun s : Finset L => (traceSize (-(Y - ∑ i ∈ s, f i))).toReal)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun s : Finset L => traceSize (-(Y - ∑ i ∈ s, f i))) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG (fun _ => zero_le)
          (fun s => ts_neg_le _)
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun s => ntn_nonneg _)
      (fun s => ntn_le_ts (tc_neg (tc_sub hY (tc_sum s f hf))))

end P45G

end

end N2W2

section N2T

open scoped BigOperators ENNReal ComplexConjugate Topology

open Filter

attribute [local instance] Classical.propDecidable

namespace P45T
noncomputable local instance (priority := 1100) scH_nacg_3 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_3 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_3 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_3 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_3 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_3 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ns_3 (X : Type) : NormedSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_3 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scC_acm_3 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scH_am_3 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_3 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_3 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_3 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_acm_3 (X Y : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_algR_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_algC_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℂ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_t2_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : T2Space (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_po_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : PartialOrder (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cstar_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : CStarAlgebra (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_sor_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_nsc_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cfcR_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_ncfcR_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_istR_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_smcR_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_star_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_tr_3 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsTopologicalRing (E →L[ℂ] E) := inferInstance

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion IsTraceClass traceSize rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff conjugateCoeff)
open QAlgorithms.Papers.Independent.Gap48.P45 (coefficientTraceHasSum boundedTracePair)
open P45Aux P45G

/-- A trace-size convergent series gives a coefficient trace series. -/
theorem chs_of_ts {T L : Type} (Y : Matrix T T ℂ) (hY : IsTraceClass Y)
    (f : L → Matrix T T ℂ) (hf : ∀ i, IsTraceClass (f i))
    (hG : Tendsto (fun G : Finset L => traceSize (Y - ∑ i ∈ G, f i)) atTop (𝓝 0)) :
    coefficientTraceHasSum f Y := by
  refine ⟨hY, hf, p39_tc hY, fun s => ?_, fun s => ?_, ?_⟩
  · rw [← bO_sum s f hf]; exact p39_tc (tc_sum s f hf)
  · rw [← bO_sum s f hf, ← bO_sub (tc_sum s f hf) hY]
    exact p39_tc (tc_sub (tc_sum s f hf) hY)
  · have hD : ∀ s : Finset L, (∑ i ∈ s, boundedOperator (f i)) - boundedOperator Y =
        boundedOperator (-(Y - ∑ i ∈ s, f i)) := fun s => by
      rw [neg_sub, bO_sub (tc_sum s f hf) hY, bO_sum s f hf]
    simp_rw [hD]
    have hup : Tendsto (fun s : Finset L => (traceSize (-(Y - ∑ i ∈ s, f i))).toReal)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun s : Finset L => traceSize (-(Y - ∑ i ∈ s, f i))) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG (fun _ => zero_le)
          (fun s => ts_neg_le _)
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun s => ntn_nonneg _)
      (fun s => ntn_le_ts (tc_neg (tc_sub hY (tc_sum s f hf))))

/-- Entry sums of a square-summable vector family. -/
noncomputable def sig {T K : Type} (phi : K → Hilbert T) : Matrix T T ℂ :=
  fun a b => ∑' k, phi k a * star (phi k b)

lemma entry_summable {T K : Type} (phi : K → Hilbert T) (hs : Summable (fun k => ‖phi k‖ ^ 2))
    (a b : T) : Summable (fun k => phi k a * star (phi k b)) := by
  refine Summable.of_norm_bounded (g := fun k => ‖phi k‖ ^ 2) hs (fun k => ?_)
  rw [norm_mul, norm_star, sq]
  exact mul_le_mul (coord_le _ _) (coord_le _ _) (norm_nonneg _) (norm_nonneg _)

/-- Masked tail of the rank-one series, as an explicit nuclear expansion. -/
theorem tail_exp {T K : Type} (g : K → ℕ) (hg : Function.Injective g) (c : ℂ)
    (phi : K → Hilbert T) (hs : Summable (fun k => ‖phi k‖ ^ 2)) (J : Finset K) :
    ∃ e : NuclearExpansion (c • sig phi - ∑ j ∈ J, c • rankOne (phi j)),
      ∑' n, ‖e.left n‖ * ‖e.right n‖ =
        ‖c‖ * ∑' k, (if k ∈ J then 0 else ‖phi k‖ ^ 2) := by
  let y : K → Hilbert T := fun k => if k ∈ J then 0 else phi k
  let Z : ℕ → Hilbert T := Function.extend g y 0
  have hy2 : ∀ k, ‖y k‖ ^ 2 = (if k ∈ J then 0 else ‖phi k‖ ^ 2) := fun k => by
    by_cases hk : k ∈ J <;> simp [y, hk]
  have hysum : Summable (fun k => ‖y k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hs
    rw [hy2]; split_ifs <;> simp
  have hN : HasSum (fun n => ‖c • Z n‖ * ‖Z n‖)
      (‖c‖ * ∑' k, (if k ∈ J then 0 else ‖phi k‖ ^ 2)) := by
    have h1 : HasSum (fun k => ‖c • y k‖ * ‖y k‖)
        (‖c‖ * ∑' k, (if k ∈ J then 0 else ‖phi k‖ ^ 2)) := by
      have := hysum.hasSum.mul_left ‖c‖
      rw [tsum_congr hy2] at this
      have e : (fun k => ‖c • y k‖ * ‖y k‖) = fun k => ‖c‖ * ‖y k‖ ^ 2 := by
        funext k; rw [norm_smul]; ring
      rw [e]; exact this
    exact ext_hasSum hg y (fun z => ‖c • z‖ * ‖z‖) (by simp) h1
  refine ⟨mkExp (fun n => c • Z n) Z hN.summable (fun a b => ?_), hN.tsum_eq⟩
  have h2 : HasSum (fun k => (c • y k) a * star (y k b))
      ((c • sig phi - ∑ j ∈ J, c • rankOne (phi j)) a b) := by
    have hfull := ((entry_summable phi hs a b).hasSum).mul_left c
    have hJ : HasSum (fun k => if k ∈ J then c * (phi k a * star (phi k b)) else 0)
        (∑ j ∈ J, c * (phi j a * star (phi j b))) := by
      have : HasSum (fun k => if k ∈ J then c * (phi k a * star (phi k b)) else 0)
          (∑ k ∈ J, if k ∈ J then c * (phi k a * star (phi k b)) else 0) :=
        hasSum_sum_of_ne_finset_zero (fun k hk => by simp [hk])
      rwa [Finset.sum_congr rfl (fun k hk => if_pos hk)] at this
    have h3 := hfull.sub hJ
    have e1 : (fun k => (c • y k) a * star (y k b)) = fun k =>
        c * (phi k a * star (phi k b)) -
          (if k ∈ J then c * (phi k a * star (phi k b)) else 0) := by
      funext k
      by_cases hk : k ∈ J
      · simp [y, hk]
      · simp [y, hk, mul_assoc]
    have e2 : (c • sig phi - ∑ j ∈ J, c • rankOne (phi j)) a b =
        c * (∑' k, phi k a * star (phi k b)) - ∑ j ∈ J, c * (phi j a * star (phi j b)) := by
      simp [sig, rankOne, Matrix.sum_apply]
    rw [e1, e2]
    exact h3
  exact ext_hasSum hg y (fun z => (c • z) a * star (z b)) (by simp) h2

/-- The masked tails tend to zero in trace size. -/
theorem tail_ts {T K : Type} [Countable K] (c : ℂ) (phi : K → Hilbert T)
    (hs : Summable (fun k => ‖phi k‖ ^ 2)) :
    Tendsto (fun J : Finset K => traceSize (c • sig phi - ∑ j ∈ J, c • rankOne (phi j)))
      atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat K
  have hm : ∀ J : Finset K, ∑' k, (if k ∈ J then 0 else ‖phi k‖ ^ 2) =
      (∑' k, ‖phi k‖ ^ 2) - ∑ j ∈ J, ‖phi j‖ ^ 2 := by
    intro J
    have h0 : HasSum (fun k => if k ∈ J then ‖phi k‖ ^ 2 else 0)
        (∑ k ∈ J, if k ∈ J then ‖phi k‖ ^ 2 else 0) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by simp [hk])
    have := hs.hasSum.sub h0
    rw [Finset.sum_congr rfl (fun k hk => if_pos hk)] at this
    rw [← this.tsum_eq]
    exact tsum_congr (fun k => by by_cases hk : k ∈ J <;> simp [hk])
  have h1 : Tendsto (fun J : Finset K => ∑ j ∈ J, ‖phi j‖ ^ 2) atTop
      (𝓝 (∑' k, ‖phi k‖ ^ 2)) := hs.hasSum
  have hlim : Tendsto (fun J : Finset K =>
      ‖c‖ * ((∑' k, ‖phi k‖ ^ 2) - ∑ j ∈ J, ‖phi j‖ ^ 2)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∑' k, ‖phi k‖ ^ 2)).sub h1
    rw [sub_self] at h
    simpa using h.const_mul ‖c‖
  have hlim' := ENNReal.tendsto_ofReal hlim
  rw [ENNReal.ofReal_zero] at hlim'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
    (fun _ => zero_le) (fun J => ?_)
  obtain ⟨e, he⟩ := tail_exp g hg c phi hs J
  exact (ts_le e).trans (by rw [he, hm])

lemma tc_smul_sig {T K : Type} [Countable K] (c : ℂ) (phi : K → Hilbert T)
    (hs : Summable (fun k => ‖phi k‖ ^ 2)) : IsTraceClass (c • sig phi) := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat K
  obtain ⟨e, _⟩ := tail_exp g hg c phi hs ∅
  have h : c • sig phi - ∑ j ∈ (∅ : Finset K), c • rankOne (phi j) = c • sig phi := by simp
  exact h ▸ ⟨e⟩

lemma tc_smul_rk {T : Type} (c : ℂ) (u : Hilbert T) : IsTraceClass (c • rankOne u) :=
  ⟨expRk c u⟩

lemma tc_rk {T : Type} (u : Hilbert T) : IsTraceClass (rankOne u) := by
  have := tc_smul_rk (1 : ℂ) u
  rwa [one_smul] at this

lemma adj_rk {I E : Type} (w : Hilbert I) (phi : Hilbert E) :
    ContinuousLinearMap.adjoint ((innerSL ℂ w).smulRight phi : Hilbert I →L[ℂ] Hilbert E) =
      (innerSL ℂ phi).smulRight w := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
    inner_smul_right, inner_conj_symm]
  ring

lemma conj_rk {I E : Type} (w : Hilbert I) (phi : Hilbert E) (X : Matrix I I ℂ) :
    conjugateCoeff ((innerSL ℂ w).smulRight phi : Hilbert I →L[ℂ] Hilbert E) X =
      inner ℂ w (boundedOperator X w) • rankOne phi := by
  unfold conjugateCoeff
  rw [adj_rk]
  have h : ((innerSL ℂ w).smulRight phi : Hilbert I →L[ℂ] Hilbert E).comp
      ((boundedOperator X).comp ((innerSL ℂ phi).smulRight w)) =
      inner ℂ w (boundedOperator X w) • rk phi phi := by
    ext1 x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, map_smul, inner_smul_right, ContinuousLinearMap.smul_apply, rk_apply,
      smul_smul]
    rw [mul_comm]
  have hc : ∀ (c : ℂ) (A : Hilbert E →L[ℂ] Hilbert E),
      operatorCoeff (c • A) = c • operatorCoeff A := fun c A => by
    funext i j; simp [operatorCoeff]
  rw [h, hc, rk_coeff]

lemma btp_rk {I : Type} (w : Hilbert I) (X : Matrix I I ℂ) :
    boundedTracePair X (boundedOperator (rankOne w)) = inner ℂ w (boundedOperator X w) := by
  rw [bO_eq (rk_coeff w)]
  unfold boundedTracePair
  have h : ∀ i, operatorCoeff ((rk w w).comp (boundedOperator X)) i i =
      star ((ContinuousLinearMap.adjoint (boundedOperator X) w) i) * w i := by
    intro i
    rw [operatorCoeff_apply, ContinuousLinearMap.comp_apply, rk_apply,
      ← ContinuousLinearMap.adjoint_inner_left, inner_single_right']
    simp
  simp_rw [h]
  rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  exact tsum_congr (fun i => by simp [mul_comm])

lemma sig_of_frame {T K : Type} (phi : K → Hilbert T) (y : Hilbert T → Hilbert T)
    (h : ∀ x, HasSum (fun k => inner ℂ (phi k) x • phi k) (y x)) (a b : T) :
    HasSum (fun k => phi k a * star (phi k b)) (y (lp.single 2 b (1 : ℂ)) a) := by
  have := hasSum_coord (h (lp.single 2 b (1 : ℂ))) a
  convert this using 1
  funext k
  rw [inner_single_right']
  simp [mul_comm]

open QAlgorithms.Papers.Independent.Gap48.P45 (BoundIndex) in
open QAlgorithms.Papers.Independent.Frontier18.P18 (IsKrausRepresentation) in
/-- N2W core: a rank-one Kraus representation |phi_ij><w_i| and rows psi_i with the
same frame operators give the whitened trace-norm series (clauses 3-4). -/
theorem n2w_core {I E L : Type} [Countable L] {m : ℕ∞}
    (Psi : Matrix I I ℂ → Matrix E E ℂ)
    (hPsi : ∀ X, IsTraceClass X → IsTraceClass (Psi X))
    (w : L → Hilbert I) (phi psi : L → BoundIndex m → Hilbert E)
    (hphi : ∀ i, HasSum (fun j => ‖phi i j‖ ^ 2) 1)
    (hpsi : ∀ i, HasSum (fun j => ‖psi i j‖ ^ 2) 1)
    (F : L → Hilbert E → Hilbert E)
    (hFpsi : ∀ i x, HasSum (fun k => inner ℂ (psi i k) x • psi i k) (F i x))
    (hFphi : ∀ i x, HasSum (fun k => inner ℂ (phi i k) x • phi i k) (F i x))
    (hK : IsKrausRepresentation Psi (fun p : L × BoundIndex m =>
      ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) : Hilbert I →L[ℂ] Hilbert E))) :
    ∃ sigma : L → Matrix E E ℂ,
      (∀ i, coefficientTraceHasSum (fun k => rankOne (psi i k)) (sigma i)) ∧
      ∀ X, IsTraceClass X → coefficientTraceHasSum (fun i => boundedTracePair X
        (boundedOperator (rankOne (w i))) • sigma i) (Psi X) := by
  have hsig : ∀ i, sig (psi i) = sig (phi i) := fun i => by
    funext a b
    exact ((sig_of_frame (psi i) (F i) (hFpsi i) a b).tsum_eq).trans
      ((sig_of_frame (phi i) (F i) (hFphi i) a b).tsum_eq).symm
  refine ⟨fun i => sig (psi i), fun i => ?_, fun X hX => ?_⟩
  · have h := tail_ts 1 (psi i) (hpsi i).summable
    simp only [one_smul] at h
    have htc := tc_smul_sig 1 (psi i) (hpsi i).summable
    rw [one_smul] at htc
    exact chs_of_ts _ htc _ (fun k => tc_rk _) h
  · have hc : ∀ p : L × BoundIndex m,
        conjugateCoeff ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) :
          Hilbert I →L[ℂ] Hilbert E) X =
        boundedTracePair X (boundedOperator (rankOne (w p.1))) • rankOne (phi p.1 p.2) :=
      fun p => by rw [conj_rk, btp_rk]
    refine group_series (Psi X) (hPsi X hX)
      (fun p => conjugateCoeff ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) :
          Hilbert I →L[ℂ] Hilbert E) X)
      (fun p => by rw [hc]; exact tc_smul_rk _ _) _
      (fun i => tc_smul_sig _ _ (hpsi i).summable) (fun i => ?_) (hK.2 X hX)
    refine (tail_ts (boundedTracePair X (boundedOperator (rankOne (w i)))) (phi i)
      (hphi i).summable).congr (fun J => ?_)
    dsimp only
    rw [hsig i]
    exact congrArg (fun Z => traceSize (_ - Z))
      (Finset.sum_congr rfl fun j _ => (hc (i, j)).symm)

end P45T

end N2T

section C4aPart

set_option autoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace

/-! C4 infrastructure for 0d372677 (Petz equality). K-a: the Parseval identity behind the
resolvent variational form Q_t(rho, sigma) = sup_W [2 Re Tr(rho W) - Tr(sigma W W*) - t Tr(rho W* W)].
Generic Hilbert space with two Hilbert bases (eigenbases of rho and sigma in the application). -/

namespace P45C4
noncomputable local instance (priority := 1100) scC_acm_4 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scA_algR_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_algC_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℂ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_t2_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : T2Space (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_po_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : PartialOrder (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cstar_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : CStarAlgebra (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_sor_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_nsc_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cfcR_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_ncfcR_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_istR_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_smcR_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_star_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_tr_4 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsTopologicalRing (E →L[ℂ] E) := inferInstance

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type}

lemma hb_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  have e1 : (fun i => ((‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) = fun i => ⟪x, b i⟫_ℂ * ⟪b i, x⟫_ℂ := by
    funext i
    rw [← inner_conj_symm x (b i), RCLike.conj_mul]
    push_cast
    rfl
  have e2 : ((‖x‖ ^ 2 : ℝ) : ℂ) = ⟪x, x⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x]
    push_cast
    rfl
  have h2 : HasSum (fun i => ((‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1, e2]
    exact h
  exact Complex.hasSum_ofReal.mp h2

lemma hasSum_prod_of_fibers {α : Type} [NormedAddCommGroup α] [CompleteSpace α]
    {f : κ × ι → α} {g : κ → α} (hf : Summable f)
    (hg : ∀ j, HasSum (fun i => f (j, i)) (g j)) : HasSum f (∑' j, g j) := by
  have := hf.hasSum.prod_fiberwise hg
  rw [this.tsum_eq]
  exact hf.hasSum

lemma summable_prod_of_fibers_nonneg {f : κ × ι → ℝ} (hf : ∀ p, 0 ≤ f p) {g : κ → ℝ}
    (hg : ∀ j, HasSum (fun i => f (j, i)) (g j)) (hgs : Summable g) : Summable f := by
  refine (summable_prod_of_nonneg (fun p => hf p)).2 ⟨fun j => (hg j).summable, ?_⟩
  simpa [fun j => (hg j).tsum_eq] using hgs

lemma hasSum_prod_of_fibers_nonneg {f : κ × ι → ℝ} (hf : ∀ p, 0 ≤ f p) {g : κ → ℝ}
    (hg : ∀ j, HasSum (fun i => f (j, i)) (g j)) (hgs : Summable g) : HasSum f (∑' j, g j) :=
  hasSum_prod_of_fibers (summable_prod_of_fibers_nonneg hf hg hgs) hg

/-- Same, with the fibres over the second coordinate. -/
lemma hasSum_prod_of_fibers_nonneg' {f : κ × ι → ℝ} (hf : ∀ p, 0 ≤ f p) {g : ι → ℝ}
    (hg : ∀ i, HasSum (fun j => f (j, i)) (g i)) (hgs : Summable g) : HasSum f (∑' i, g i) := by
  have h := hasSum_prod_of_fibers_nonneg (f := fun q : ι × κ => f (q.2, q.1))
    (fun q => hf _) hg hgs
  exact ((Equiv.prodComm ι κ).hasSum_iff (f := f)).mp h





/-- K-eig: a compact self-adjoint operator has a Hilbert basis of eigenvectors with real eigenvalues. -/
theorem exists_eigenbasis (T : E →L[ℂ] E) (hc : IsCompactOperator T)
    (hs : (T : E →ₗ[ℂ] E).IsSymmetric) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ E) (lam : ι → ℝ), ∀ i, T (b i) = (lam i : ℂ) • b i := by
  classical
  let V : ℂ → Submodule ℂ E := fun μ => Module.End.eigenspace (T : Module.End ℂ E) μ
  have hVc : ∀ μ, IsClosed (V μ : Set E) := by
    intro μ
    have : (V μ : Set E) = (fun x => T x - μ • x) ⁻¹' {0} := by
      ext x
      simp only [V, SetLike.mem_coe, Module.End.mem_eigenspace_iff, Set.mem_preimage,
        Set.mem_singleton_iff, sub_eq_zero]
      rfl
    rw [this]
    exact isClosed_singleton.preimage (T.continuous.sub (continuous_const_smul μ))
  haveI : ∀ μ, CompleteSpace (V μ) := fun μ => (hVc μ).completeSpace_coe
  choose w b _hb using fun μ => exists_hilbertBasis ℂ (V μ)
  let v : (Σ μ : ℂ, w μ) → E := fun p => ((b p.1 p.2 : V p.1) : E)
  have hon : Orthonormal ℂ v :=
    hs.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal (fun μ => (b μ).orthonormal)
  have hle : ∀ μ, V μ ≤ (Submodule.span ℂ (Set.range v))ᗮᗮ := by
    intro μ y hy
    rw [Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
      Submodule.topologicalClosure_coe]
    have hy' : (⟨y, hy⟩ : V μ) ∈ closure (Submodule.span ℂ (Set.range (b μ)) : Set (V μ)) := by
      rw [← Submodule.topologicalClosure_coe, (b μ).dense_span]
      trivial
    refine map_mem_closure continuous_subtype_val hy' (fun z hz => ?_)
    have hz' : (z : E) ∈ (Submodule.span ℂ (Set.range (b μ))).map (V μ).subtype :=
      Submodule.mem_map_of_mem hz
    rw [Submodule.map_span] at hz'
    refine Submodule.span_mono ?_ hz'
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨⟨μ, k⟩, rfl⟩
  have hbot : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    have h1 : (⨆ μ, V μ) ≤ (Submodule.span ℂ (Set.range v))ᗮᗮ := iSup_le hle
    have h2 := Submodule.orthogonal_le h1
    have h3 := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs
    refine eq_bot_iff.mpr ?_
    calc (Submodule.span ℂ (Set.range v))ᗮ ≤ (Submodule.span ℂ (Set.range v))ᗮᗮᗮ :=
          Submodule.le_orthogonal_orthogonal _
      _ ≤ (⨆ μ, V μ)ᗮ := h2
      _ = ⊥ := h3
      _ ≤ ⊥ := le_rfl
  refine ⟨Σ μ : ℂ, w μ, HilbertBasis.mkOfOrthogonalEqBot hon hbot, fun p => p.1.re, fun p => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hmem : v p ∈ V p.1 := (b p.1 p.2).2
  have hne : v p ≠ 0 := by
    intro h0
    have := hon.1 p
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hev : Module.End.HasEigenvalue (T : Module.End ℂ E) p.1 :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩
  have hreal := hs.conj_eigenvalue_eq_self hev
  have hre : ((p.1.re : ℝ) : ℂ) = p.1 := Complex.conj_eq_iff_re.mp hreal
  rw [hre]
  exact Module.End.mem_eigenspace_iff.mp hmem

section Trunc

attribute [local instance] Classical.propDecidable

variable (e : HilbertBasis ι ℂ E) (f : HilbertBasis κ ℂ E) (r : ι → ℝ) (s : κ → ℝ) (t : ℝ)

/-- The value of the resolvent variational problem at W (in eigen coordinates). -/
def val (W : E →L[ℂ] E) : ℝ :=
  2 * (∑' i, r i * (⟪e i, W (e i)⟫_ℂ).re) - ∑' j, s j * ‖(ContinuousLinearMap.adjoint W) (f j)‖ ^ 2
    - t * ∑' i, r i * ‖W (e i)‖ ^ 2


/-- The optimal coefficients y_ji = c_ji r_i / (s_j + t r_i). -/
def yc (p : κ × ι) : ℂ := ((r p.2 / (s p.1 + t * r p.2) : ℝ) : ℂ) * ⟪f p.1, e p.2⟫_ℂ

/-- Finite-rank truncation of the optimiser. -/
def truncOp (F : Finset (κ × ι)) : E →L[ℂ] E :=
  ∑ p ∈ F, yc e f r s t p • InnerProductSpace.rankOne ℂ (f p.1) (e p.2)


variable {r s t}






end Trunc

section Compact

lemma rankOne_compact (x y : E) : IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  have h := (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x)
  have heq : ⇑(InnerProductSpace.rankOne ℂ x y) =
      ⇑(ContinuousLinearMap.toSpanSingleton ℂ x) ∘ ⇑(innerSL ℂ y) := by
    funext z
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [heq]
  exact h

lemma norm_rankOne_le (x y : E) : ‖InnerProductSpace.rankOne ℂ x y‖ ≤ ‖x‖ * ‖y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun z => ?_)
  rw [InnerProductSpace.rankOne_apply, norm_smul]
  calc ‖⟪y, z⟫_ℂ‖ * ‖x‖ ≤ (‖y‖ * ‖z‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (norm_inner_le_norm y z) (norm_nonneg _)
    _ = ‖x‖ * ‖y‖ * ‖z‖ := by ring



end Compact

section Eigen



/-- Eigen expansion T x = Sum r_i <e_i, x> e_i. -/
theorem eigen_expand {T : E →L[ℂ] E} (e : HilbertBasis ι ℂ E) (r : ι → ℝ)
    (hT : ∀ i, T (e i) = (r i : ℂ) • e i) (x : E) :
    HasSum (fun i => ((r i : ℂ) * ⟪e i, x⟫_ℂ) • e i) (T x) := by
  have h := (e.hasSum_repr x).mapL T
  simp only [map_smul, hT, smul_smul, HilbertBasis.repr_apply_apply] at h
  convert h using 2 with i
  ring_nf

end Eigen

section Forms

variable (f : E → E → ℂ)
    (H1 : ∀ x1 x2 y, f (x1 + x2) y = f x1 y + f x2 y)
    (H2 : ∀ (c : ℂ) x y, f (c • x) y = (starRingEnd ℂ) c * f x y)
    (H3 : ∀ x y1 y2, f x (y1 + y2) = f x y1 + f x y2)
    (H4 : ∀ (c : ℂ) x y, f x (c • y) = c * f x y)
include H1 H2 H3 H4







end Forms

end P45C4


end

end C4aPart

section N2W1

set_option autoImplicit false

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace P45W
noncomputable local instance (priority := 1100) scC_acm_5 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_top_5 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : TopologicalSpace (E →L[ℂ] F) := inferInstance
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

open QAlgorithms.Papers.Independent.Gap48.P45 (BoundIndex)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma rk_summable {M : Type} (phi : M → E) (hs : Summable (fun j => ‖phi j‖ ^ 2)) :
    Summable (fun j => InnerProductSpace.rankOne ℂ (phi j) (phi j)) :=
  Summable.of_norm_bounded hs (fun j => by
    calc _ ≤ ‖phi j‖ * ‖phi j‖ := P45C4.norm_rankOne_le _ _
      _ = ‖phi j‖ ^ 2 := by ring)

/-- The frame operator `S = Σ_j |φ_j⟩⟨φ_j|`. -/
def frameOp {M : Type} (phi : M → E) : E →L[ℂ] E :=
  ∑' j, InnerProductSpace.rankOne ℂ (phi j) (phi j)

lemma frameOp_hasSum {M : Type} (phi : M → E) (hs : Summable (fun j => ‖phi j‖ ^ 2)) (x : E) :
    HasSum (fun j => inner ℂ (phi j) x • phi j) (frameOp phi x) := by
  have h := ((rk_summable phi hs).hasSum).mapL (ContinuousLinearMap.apply ℂ E x)
  simpa [InnerProductSpace.rankOne_apply, frameOp] using h

lemma frameOp_compact {M : Type} (phi : M → E) (hs : Summable (fun j => ‖phi j‖ ^ 2)) :
    IsCompactOperator (frameOp phi) := by
  refine isCompactOperator_of_tendsto (rk_summable phi hs).hasSum
    (Filter.Eventually.of_forall (fun F => ?_))
  induction F using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | insert k F hk ih =>
    rw [Finset.sum_insert hk]
    exact (P45C4.rankOne_compact _ _).add ih

lemma frameOp_symm {M : Type} (phi : M → E) (hs : Summable (fun j => ‖phi j‖ ^ 2)) :
    ((frameOp phi : E →L[ℂ] E) : E →ₗ[ℂ] E).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  have h1 := (frameOp_hasSum phi hs x).mapL (innerSL ℂ y)
  have h2 := (frameOp_hasSum phi hs y).mapL (innerSL ℂ x)
  simp only [innerSL_apply_apply, inner_smul_right] at h1 h2
  have h3 := h1.star
  rw [← inner_conj_symm (frameOp phi x) y]
  refine h3.unique ?_
  convert h2 using 1
  funext j
  simp only [star_mul', RCLike.star_def, inner_conj_symm]
  ring

theorem frame_eigen {M : Type} (phi : M → E) (hs : HasSum (fun j => ‖phi j‖ ^ 2) 1) :
    ∃ (ι : Type) (e : HilbertBasis ι ℂ E) (r : ι → ℝ), (∀ k, 0 ≤ r k) ∧ HasSum r 1 ∧
      ∀ k, frameOp phi (e k) = (r k : ℂ) • e k := by
  obtain ⟨ι, e, lam, hlam⟩ := P45C4.exists_eigenbasis (frameOp phi)
    (frameOp_compact phi hs.summable) (frameOp_symm phi hs.summable)
  have hval : ∀ k, HasSum (fun j => ‖inner ℂ (phi j) (e k)‖ ^ 2) (lam k) := by
    intro k
    have h1 := (frameOp_hasSum phi hs.summable (e k)).mapL (innerSL ℂ (e k))
    simp only [innerSL_apply_apply] at h1
    rw [hlam k, inner_smul_right, inner_self_eq_norm_sq_to_K, e.orthonormal.1 k] at h1
    have hf : (fun j => inner ℂ (e k) (inner ℂ (phi j) (e k) • phi j)) =
        fun j => ((‖inner ℂ (phi j) (e k)‖ ^ 2 : ℝ) : ℂ) := by
      funext j
      rw [inner_smul_right, ← inner_conj_symm (phi j) (e k), mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.norm_conj]
    rw [hf] at h1
    have h2 : HasSum (fun j => ((‖inner ℂ (phi j) (e k)‖ ^ 2 : ℝ) : ℂ)) ((lam k : ℝ) : ℂ) := by
      simpa using h1
    exact Complex.hasSum_ofReal.mp h2
  have hnn : ∀ k, 0 ≤ lam k := fun k => (hval k).nonneg (fun _ => sq_nonneg _)
  refine ⟨ι, e, lam, hnn, ?_, hlam⟩
  have hf : HasSum (fun p : ι × M => ‖inner ℂ (phi p.2) (e p.1)‖ ^ 2) (∑' j, ‖phi j‖ ^ 2) :=
    P45C4.hasSum_prod_of_fibers_nonneg' (f := fun p : ι × M => ‖inner ℂ (phi p.2) (e p.1)‖ ^ 2)
      (fun _ => sq_nonneg _)
      (fun j => by
        have := P45C4.hb_norm_sq e (phi j)
        simpa only [norm_inner_symm] using this) hs.summable
  rw [hs.tsum_eq] at hf
  exact hf.prod_fiberwise (fun k => hval k)

lemma boundIndex_finite (n : ℕ) : Finite (BoundIndex (n : ℕ∞)) :=
  Finite.of_injective (fun k : BoundIndex (n : ℕ∞) => (⟨k.1, by exact_mod_cast k.2⟩ : Fin n))
    (fun a b h => Subtype.ext (by simpa using congrArg Fin.val h))

/-- Orthogonal rows: a unit-trace frame `φ` indexed by `BoundIndex m` has an orthogonal
family `ψ` on the same index set with the same frame operator and `Σ ‖ψ_k‖² = 1`. -/
theorem orth_rows {m : ℕ∞} (phi : BoundIndex m → E) (hs : HasSum (fun j => ‖phi j‖ ^ 2) 1) :
    ∃ psi : BoundIndex m → E, HasSum (fun k => ‖psi k‖ ^ 2) 1 ∧
      (∀ p t, p ≠ t → inner ℂ (psi t) (psi p) = 0) ∧
      ∀ x, HasSum (fun k => inner ℂ (psi k) x • psi k) (frameOp phi x) := by
  obtain ⟨ι, e, r, hr0, hr1, hrS⟩ := frame_eigen phi hs
  have hemb : Nonempty (Function.support r ↪ BoundIndex m) := by
    cases m using ENat.recTopCoe with
    | top =>
      haveI : Countable (Function.support r) := hr1.summable.countable_support.to_subtype
      obtain ⟨f, hf⟩ := Countable.exists_injective_nat (Function.support r)
      exact ⟨⟨fun k => ⟨f k, ENat.coe_lt_top _⟩, fun a b h => hf (congrArg Subtype.val h)⟩⟩
    | coe n =>
      haveI := boundIndex_finite n
      letI := Fintype.ofFinite (BoundIndex (n : ℕ∞))
      have hmem : ∀ k : Function.support r, e k ∈ Submodule.span ℂ (Set.range phi) := by
        intro k
        have hk : (r k : ℂ) ≠ 0 := by exact_mod_cast k.2
        have hS : ∀ y, frameOp phi y ∈ Submodule.span ℂ (Set.range phi) := by
          intro y
          rw [(frameOp_hasSum phi hs.summable y).unique (hasSum_fintype _)]
          exact Submodule.sum_mem _ (fun j _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
        have he : (e k : E) = ((r k : ℂ))⁻¹ • frameOp phi (e k) := by
          rw [hrS k, inv_smul_smul₀ hk]
        rw [he]
        exact Submodule.smul_mem _ _ (hS _)
      have hli : LinearIndependent ℂ (fun k : Function.support r =>
          (⟨e k, hmem k⟩ : Submodule.span ℂ (Set.range phi))) := by
        refine LinearIndependent.of_comp (Submodule.span ℂ (Set.range phi)).subtype ?_
        exact (e.orthonormal.comp _ Subtype.val_injective).linearIndependent
      have h1 := hli.cardinal_le_rank
      have h2 := rank_span_le (R := ℂ) (Set.range phi)
      have h3 := Cardinal.mk_range_le (f := phi)
      exact (Cardinal.le_def _ _).mp (h1.trans (h2.trans h3))
  obtain ⟨g⟩ := hemb
  let f0 : Function.support r → E := fun k => ((Real.sqrt (r k) : ℝ) : ℂ) • e k
  let psi : BoundIndex m → E := Function.extend (⇑g) f0 (fun _ => (0 : E))
  have hpg : ∀ k, psi (g k) = f0 k := fun k => g.injective.extend_apply f0 (fun _ => (0 : E)) k
  have hpo : ∀ t, t ∉ Set.range g → psi t = 0 := fun t ht => by
    simp only [psi]
    rw [Function.extend_apply' f0 (fun _ => (0 : E)) t (fun ⟨a, ha⟩ => ht ⟨a, ha⟩)]
  have hsq : ∀ k : Function.support r, ((Real.sqrt (r k) : ℂ)) * (Real.sqrt (r k) : ℂ) = r k := by
    intro k; exact_mod_cast Real.mul_self_sqrt (hr0 k)
  refine ⟨psi, ?_, ?_, ?_⟩
  · refine (g.injective.hasSum_iff (fun t ht => by rw [hpo t ht]; simp)).mp ?_
    have hfun : (fun t => ‖psi t‖ ^ 2) ∘ g = fun k : Function.support r => r k := by
      funext k
      simp only [Function.comp_apply, hpg, f0, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), e.orthonormal.1 k, mul_one,
        Real.sq_sqrt (hr0 k)]
    rw [hfun]
    exact hasSum_subtype_support.mpr hr1
  · intro p t hpt
    by_cases hp : p ∈ Set.range g
    · by_cases ht : t ∈ Set.range g
      · obtain ⟨a, rfl⟩ := hp
        obtain ⟨b, rfl⟩ := ht
        have hab : (b : ι) ≠ a := fun h => hpt (by rw [Subtype.ext h])
        rw [hpg, hpg]
        simp only [f0, inner_smul_left, inner_smul_right, e.orthonormal.2 hab, mul_zero]
      · rw [hpo t ht, inner_zero_left]
    · rw [hpo p hp, inner_zero_right]
  · intro x
    refine (g.injective.hasSum_iff (fun t ht => by rw [hpo t ht]; simp)).mp ?_
    have hfun : (fun t => inner ℂ (psi t) x • psi t) ∘ g =
        (fun k => ((r k : ℂ) * inner ℂ (e k) x) • e k) ∘ (Subtype.val : Function.support r → ι) := by
      funext k
      simp only [Function.comp_apply, hpg, f0, inner_smul_left, Complex.conj_ofReal, smul_smul]
      congr 1
      linear_combination (inner ℂ (e k) x) * hsq k
    rw [hfun]
    refine (hasSum_subtype_iff_of_support_subset ?_).mpr (P45C4.eigen_expand e r hrS x)
    intro k hk
    by_contra h0
    simp only [Function.mem_support, not_not] at h0
    exact hk (by simp [h0])

end P45W

end

end N2W1

section N2WG

open scoped BigOperators ENNReal Topology

namespace P45N2W
noncomputable local instance (priority := 1100) scH_nacg_6 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_6 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_6 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_6 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_6 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_6 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_6 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_6 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_algR_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_algC_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℂ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_t2_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : T2Space (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_po_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : PartialOrder (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cstar_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : CStarAlgebra (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_sor_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_nsc_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cfcR_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_ncfcR_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_istR_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_smcR_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_star_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_tr_6 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsTopologicalRing (E →L[ℂ] E) := inferInstance

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsTraceClass rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator IsKrausRepresentation)
open QAlgorithms.Papers.Independent.Gap48.P45 (BoundIndex NormalizedOrthogonalRows
  coefficientTraceHasSum boundedTracePair)

theorem n2w {I E L : Type} [Countable L] (m : ℕ∞) (Psi : Channel I E) (w : L → Hilbert I)
    (phi : L → BoundIndex m → Hilbert E) (hphi : ∀ i, HasSum (fun j => ‖phi i j‖ ^ 2) 1)
    (hK : IsKrausRepresentation Psi.val (fun p : L × BoundIndex m =>
      ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) : Hilbert I →L[ℂ] Hilbert E))) :
    ∃ psi : L → BoundIndex m → Hilbert E, NormalizedOrthogonalRows psi ∧
      ∃ sigma : L → Matrix E E ℂ,
        (∀ i, coefficientTraceHasSum (fun k => rankOne (psi i k)) (sigma i)) ∧
        ∀ X, IsTraceClass X → coefficientTraceHasSum (fun i => boundedTracePair X
          (boundedOperator (rankOne (w i))) • sigma i) (Psi.val X) := by
  choose psi hpsi1 hpsi2 hpsi3 using fun i => P45W.orth_rows (phi i) (hphi i)
  obtain ⟨sigma, h3, h4⟩ := P45T.n2w_core Psi.val Psi.2.1 w phi psi hphi hpsi1
    (fun i => P45W.frameOp (phi i)) hpsi3
    (fun i x => P45W.frameOp_hasSum (phi i) (hphi i).summable x) hK
  exact ⟨psi, ⟨hpsi1, fun k p t hpt => hpsi2 k p t hpt⟩, sigma, h3, h4⟩

end P45N2W

end N2WG

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


open QAlgorithms.Papers.Independent.Gap48.P45 QAlgorithms.Papers.Independent.Dependency50.P33 QAlgorithms.Papers.Independent.Frontier18.P01 QAlgorithms.Papers.Independent.Frontier18.P07 QAlgorithms.Papers.Independent.Frontier18.P18 in
theorem solution
    {I E L : Type} [Countable L] (m : ℕ∞) (Psi : Channel I E) (w : L → Hilbert I)
    (phi : L → BoundIndex m → Hilbert E) (hphi : ∀ i, HasSum (fun j => ‖phi i j‖ ^ 2) 1)
    (hK : IsKrausRepresentation Psi.val (fun p : L × BoundIndex m =>
      ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) : Hilbert I →L[ℂ] Hilbert E))) :
    ∃ psi : L → BoundIndex m → Hilbert E, NormalizedOrthogonalRows psi ∧
      ∃ sigma : L → Matrix E E ℂ,
        (∀ i, coefficientTraceHasSum (fun k => rankOne (psi i k)) (sigma i)) ∧
        ∀ X, IsTraceClass X → coefficientTraceHasSum (fun i => boundedTracePair X
          (boundedOperator (rankOne (w i))) • sigma i) (Psi.val X) := by
  exact P45N2W.n2w m Psi w phi hphi hK

end

end ChildRoot
