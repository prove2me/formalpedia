-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.pure_family_whitened_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:37:51.937347+00:00
-- url     : https://prove2.me/submissions/2727c7a6-f415-4844-91a2-8a4bf85dedd4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
set_option Elab.async false

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false



set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal ComplexConjugate Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace P45Petz
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

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsDensity IsTraceClassChannel traceSize NuclearExpansion tensorApply)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats)
open QAlgorithms.Papers.Independent.Frontier18.P18 (ReversibleOn boundedOperator operatorCoeff conjugateCoeff)

/-! Generic shortcut instances on bounded operators (speed: TC search on `E →L[ℂ] E` is slow). -/
section GSC
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
end GSC

/-! Shortcut instances for `Hilbert T = lp (fun _ => ℂ) 2` (speed: TC search on lp is slow). -/


/-! Shortcut instances on operators (speed). -/



/-! Helpers copied from scratch/probe/176d3efb_Aall.lean (P45D, compiled there). -/
lemma norm_coord_le {T : Type} (x : Hilbert T) (t : T) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by norm_num) x t

/-! ## K3.1 balanced nuclear expansions -/


/-! ## K3.2 frame polarization -/



/-! ## K3.5 expansions over a countable index, trace-class closure -/

lemma hasSum_prod_fin {T A α : Type} [Fintype A] [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] {f : T × A → α} {g : A → α}
    (h : ∀ a, HasSum (fun t => f (t, a)) (g a)) : HasSum f (∑ a, g a) := by
  have hF : ∀ a, HasSum (fun p : T × A => if p.2 = a then f p else 0) (g a) := by
    intro a
    have hi : Function.Injective (fun t : T => ((t, a) : T × A)) :=
      fun x y hxy => by simpa using hxy
    have h0 : ∀ p ∉ Set.range (fun t : T => ((t, a) : T × A)),
        (fun p : T × A => if p.2 = a then f p else 0) p = 0 := by
      intro p hp
      have hne : p.2 ≠ a := by
        intro h2
        exact hp ⟨p.1, by rw [← h2]⟩
      simp [hne]
    refine (hi.hasSum_iff h0).mp ?_
    show HasSum (fun t => if ((t, a) : T × A).2 = a then f (t, a) else 0) (g a)
    simpa using h a
  have := hasSum_sum (s := Finset.univ) (fun a _ => hF a)
  convert this using 1
  funext p
  simp

lemma traceSize_le_of_countable {T ι : Type} [Countable ι] {Y : Matrix T T ℂ}
    (u v : ι → Hilbert T) (hs : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hY : ∀ a b, HasSum (fun i => u i a * star (v i b)) (Y a b)) :
    IsTraceClass Y ∧ traceSize Y ≤ ENNReal.ofReal (∑' i, ‖u i‖ * ‖v i‖) := by
  let _ : Encodable ι := Encodable.ofCountable ι
  let L : ℕ → Hilbert T := fun m => match Encodable.decode₂ ι m with
    | some i => u i
    | none => 0
  let R : ℕ → Hilbert T := fun m => match Encodable.decode₂ ι m with
    | some i => v i
    | none => 0
  have hL : ∀ i, L (Encodable.encode i) = u i := fun i => by simp [L, Encodable.encodek₂]
  have hR : ∀ i, R (Encodable.encode i) = v i := fun i => by simp [R, Encodable.encodek₂]
  have hout : ∀ m, m ∉ Set.range (Encodable.encode (α := ι)) → L m = 0 ∧ R m = 0 := by
    intro m hm
    have h0 : Encodable.decode₂ ι m = none := by
      rcases h : Encodable.decode₂ ι m with _ | i
      · rfl
      · exact absurd ⟨i, Encodable.decode₂_eq_some.mp h⟩ hm
    simp [L, R, h0]
  have hinj : Function.Injective (Encodable.encode (α := ι)) := Encodable.encode_injective
  have hsN : HasSum (fun m => ‖L m‖ * ‖R m‖) (∑' i, ‖u i‖ * ‖v i‖) := by
    refine (hinj.hasSum_iff (fun m hm => by simp [(hout m hm).1])).mp ?_
    have h1 : ((fun m => ‖L m‖ * ‖R m‖) ∘ Encodable.encode) = fun i => ‖u i‖ * ‖v i‖ := by
      funext i; simp only [Function.comp, hL, hR]
    rw [h1]; exact hs.hasSum
  have hcoef : ∀ a b, HasSum (fun m => L m a * star (R m b)) (Y a b) := by
    intro a b
    refine (hinj.hasSum_iff (fun m hm => by simp [(hout m hm).1])).mp ?_
    have h1 : ((fun m => L m a * star (R m b)) ∘ Encodable.encode) =
        fun i => u i a * star (v i b) := by
      funext i; simp only [Function.comp, hL, hR]
    rw [h1]; exact hY a b
  let e : NuclearExpansion Y := ⟨L, R, hsN.summable, fun a b => (hcoef a b).tsum_eq.symm⟩
  refine ⟨⟨e⟩, ?_⟩
  unfold traceSize
  refine (iInf_le _ e).trans (le_of_eq ?_)
  congr 1
  exact hsN.tsum_eq

lemma coeff_hasSum {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) (i j : T) :
    HasSum (fun n => e.left n i * star (e.right n j)) (X i j) := by
  rw [e.coefficients i j]
  refine (Summable.of_norm_bounded e.summable (fun n => ?_)).hasSum
  rw [norm_mul, norm_star]
  exact mul_le_mul (norm_coord_le _ _) (norm_coord_le _ _) (norm_nonneg _) (norm_nonneg _)

lemma tc_add {T : Type} {X Y : Matrix T T ℂ} (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    IsTraceClass (X + Y) := by
  obtain ⟨e1⟩ := hX
  obtain ⟨e2⟩ := hY
  refine (traceSize_le_of_countable (ι := ℕ × Bool)
    (fun p => if p.2 then e1.left p.1 else e2.left p.1)
    (fun p => if p.2 then e1.right p.1 else e2.right p.1) ?_ ?_).1
  · refine (hasSum_prod_fin (g := fun b : Bool => if b then ∑' n, ‖e1.left n‖ * ‖e1.right n‖
      else ∑' n, ‖e2.left n‖ * ‖e2.right n‖) (fun b => ?_)).summable
    cases b
    · simpa using e2.summable.hasSum
    · simpa using e1.summable.hasSum
  · intro a b
    have h := hasSum_prod_fin (f := fun p : ℕ × Bool =>
      (if p.2 then e1.left p.1 else e2.left p.1) a *
        star ((if p.2 then e1.right p.1 else e2.right p.1) b))
      (g := fun c : Bool => if c then X a b else Y a b) (fun c => by
        cases c
        · simpa using coeff_hasSum e2 a b
        · simpa using coeff_hasSum e1 a b)
    convert h using 1
    simp [Matrix.add_apply, add_comm]

lemma tc_smul {T : Type} (c : ℂ) {X : Matrix T T ℂ} (hX : IsTraceClass X) :
    IsTraceClass (c • X) := by
  obtain ⟨e⟩ := hX
  refine (traceSize_le_of_countable (ι := ℕ) (fun n => c • e.left n) e.right ?_ ?_).1
  · refine (e.summable.mul_left ‖c‖).congr (fun n => ?_)
    rw [norm_smul]; ring
  · intro a b
    have h := (coeff_hasSum e a b).mul_left c
    have h' : (fun n => (c • e.left n) a * star (e.right n b)) =
        fun n => c * (e.left n a * star (e.right n b)) := by
      funext n; simp [mul_assoc]
    rw [h', Matrix.smul_apply, smul_eq_mul]; exact h

lemma tc_zero {T : Type} : IsTraceClass (0 : Matrix T T ℂ) := by
  refine (traceSize_le_of_countable (ι := ℕ) (fun _ => (0 : Hilbert T)) (fun _ => 0) ?_ ?_).1
  · simp
  · intro a b; simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℂ)) 0)




/-! ## K3.6 positive pieces `Mat w = Σ_n |w_n><w_n|` -/


def Mat {T : Type} (w : ℕ → Hilbert T) : Matrix T T ℂ := fun i j => ∑' n, w n i * star (w n j)









/-! ## C0: channels map density arrays to density arrays (n = 1 amplification). -/

lemma memℓp_two_iff' {T : Type} (f : T → ℂ) : Memℓp f 2 ↔ Summable (fun t => ‖f t‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simp

lemma hasSum_normSq {T : Type} (x : Hilbert T) : HasSum (fun t => ‖x t‖ ^ 2) (‖x‖ ^ 2) := by
  have := lp.hasSum_norm (by norm_num : 0 < (2:ℝ≥0∞).toReal) x
  simpa using this

/-- Reindex a Hilbert vector along an equivalence of labels. -/
def reindexV {T U : Type} (e : T ≃ U) (x : Hilbert U) : Hilbert T :=
  ⟨fun t => x (e t), (memℓp_two_iff' _).mpr
    ((e.summable_iff (f := fun u => ‖x u‖ ^ 2)).mpr (hasSum_normSq x).summable)⟩






/-! More helpers copied from scratch/probe/176d3efb_Aall.lean. -/
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




/-! ## Trace preservation on all of trace class -/






/-! ## K3.4 conjugating a nuclear expansion: `boundedConjugation` and `traceFirst` -/

/-! ## Square roots and Hilbert-Schmidt cyclicity -/

lemma psr_eq_sqrt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hA : 0 ≤ A) :
    QAlgorithms.Papers.Independent.Next46.P31.positiveSquareRoot A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA, cfcₙ_eq_cfc, cfc_real_eq_complex Real.sqrt hA.isSelfAdjoint]
  rfl

/-- The standard basis vector. -/
def bvec {T : Type} (k : T) : Hilbert T := lp.single 2 k (1 : ℂ)

lemma inner_bvec_left {T : Type} (k : T) (x : Hilbert T) : inner ℂ (bvec k) x = x k := by
  simp [bvec, lp.inner_single_left]

lemma coord_eq_inner {T : Type} (x : Hilbert T) (k : T) : x k = inner ℂ (bvec k) x :=
  (inner_bvec_left k x).symm

lemma sa_swap {T : Type} {t : Hilbert T →L[ℂ] Hilbert T} (ht : ContinuousLinearMap.adjoint t = t)
    (x y : Hilbert T) : inner ℂ x (t y) = inner ℂ (t x) y := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ht]



open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
lemma psr_facts {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : E →L[ℂ] E) (hP : 0 ≤ P) :
    ContinuousLinearMap.adjoint (positiveSquareRoot P) = positiveSquareRoot P ∧
      positiveSquareRoot P * positiveSquareRoot P = P := by
  rw [psr_eq_sqrt P hP]
  exact ⟨(CFC.sqrt_nonneg P).isSelfAdjoint.adjoint_eq, CFC.sqrt_mul_sqrt_self P hP⟩

lemma sa_norm_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {t P : E →L[ℂ] E} (ht : ContinuousLinearMap.adjoint t = t) (htt : t * t = P) (x : E) :
    ‖t x‖ ^ 2 = (inner ℂ x (P x)).re := by
  rw [← htt, @norm_sq_eq_re_inner ℂ]
  change RCLike.re (inner ℂ (t x) (t x)) = (inner ℂ x (t (t x))).re
  have h := ContinuousLinearMap.adjoint_inner_left t x (t x)
  rw [ht] at h
  rw [← h, ← inner_conj_symm, RCLike.conj_re]
  rfl


/-! Helpers copied from scratch/probe/176d3efb_childB.lean (proved there). -/
lemma hasSum_coord {I ι : Type} {f : ι → Hilbert I} {x : Hilbert I} (h : HasSum f x) (i : I) :
    HasSum (fun n => f n i) (x i) :=
  h.map (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i) (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i).continuous

lemma hasSum_basis {I : Type} (x : Hilbert I) :
    HasSum (fun j => x j • (lp.single 2 j (1 : ℂ) : Hilbert I)) x := by
  have h := lp.hasSum_single (E := fun _ : I => ℂ) (p := 2) (by simp) x
  have e : (fun j => x j • (lp.single 2 j (1 : ℂ) : Hilbert I)) = fun j => lp.single 2 j (x j) := by
    funext j; rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [e]; exact h

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



/-! ## Part C: Cauchy-Schwarz on coordinates and the trace formula -/
lemma coeff_bO {T : Type} {X : Matrix T T ℂ} (h : IsTraceClass X) :
    operatorCoeff (boundedOperator X) = X := by
  obtain ⟨e⟩ := h
  rw [bO_nuc e, nucOp_coeff e]



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



/-! ## L4: the square root of a state is self-adjoint Hilbert-Schmidt with HS norm 1 -/

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
lemma sqrt_state {T : Type} (rho : State T) :
    ContinuousLinearMap.adjoint (positiveSquareRoot (boundedOperator rho.coefficients)) =
        positiveSquareRoot (boundedOperator rho.coefficients) ∧
      positiveSquareRoot (boundedOperator rho.coefficients) *
        positiveSquareRoot (boundedOperator rho.coefficients) = boundedOperator rho.coefficients ∧
      HasSum (fun k => ‖positiveSquareRoot (boundedOperator rho.coefficients) (bvec k)‖ ^ 2) 1 := by
  have hP : 0 ≤ boundedOperator rho.coefficients :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (bO_pos rho)
  obtain ⟨h1, h2⟩ := psr_facts _ hP
  refine ⟨h1, h2, ?_⟩
  have hk : ∀ k, ‖positiveSquareRoot (boundedOperator rho.coefficients) (bvec k)‖ ^ 2 =
      (rho.coefficients k k).re := by
    intro k
    rw [sa_norm_sq h1 h2, inner_bvec_left]
    have := congrFun (congrFun (coeff_bO rho.density.1) k) k
    rw [← this]
    rfl
  simp_rw [hk]
  obtain ⟨_, _, hs, ht⟩ := rho.density
  rw [← ht]; exact hs.hasSum

/-! ## s3: Douglas factorization and positivity of channel outputs -/
open ContinuousLinearMap in
/-- Douglas factorization: if ‖R x‖ ≤ C ‖t x‖, t self-adjoint with t*t = P, then there is B
supported on the closure of range P with t B t = R* R. -/
lemma douglas {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (t P R : E →L[ℂ] E) (ht : adjoint t = t) (htt : t * t = P) (C : ℝ)
    (hR : ∀ x, ‖R x‖ ≤ C * ‖t x‖) :
    ∃ B : E →L[ℂ] E,
      ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection).comp
          (B.comp ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection)) = B ∧
      t.comp (B.comp t) = (adjoint R).comp R := by
  set K := (LinearMap.range P.toLinearMap).topologicalClosure with hK
  have hmem : ∀ x, t x ∈ K := by
    intro x
    rw [hK, ← Submodule.orthogonal_orthogonal_eq_closure]
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [Submodule.mem_orthogonal'] at hu
    have h1 : inner ℂ u (P u) = 0 := hu (P u) ⟨u, rfl⟩
    have h2 : t u = 0 := by
      have : inner ℂ (t u) (t u) = 0 := by
        rw [← adjoint_inner_right, ht, ← h1, ← htt]; rfl
      exact inner_self_eq_zero.mp this
    rw [← adjoint_inner_left, ht, h2, inner_zero_left]
  let e : E →ₗ[ℂ] K := LinearMap.codRestrict K t.toLinearMap hmem
  have he : ∀ x, ((e x : K) : E) = t x := fun x => rfl
  have hdense : DenseRange e := by
    rw [DenseRange, Subtype.dense_iff]
    intro y hy
    have hsub : (K : Set E) ⊆ closure (Set.range t) := by
      rw [hK, Submodule.topologicalClosure_coe]
      refine closure_mono ?_
      rintro _ ⟨u, rfl⟩
      refine ⟨t u, ?_⟩
      rw [← htt]; rfl
    have hr : Set.range t = Subtype.val '' Set.range e := by
      ext z; constructor
      · rintro ⟨u, rfl⟩; exact ⟨e u, ⟨u, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨u, rfl⟩, rfl⟩; exact ⟨u, rfl⟩
    have h3 := hsub hy
    rw [hr] at h3
    exact h3
  have hnorm : ∃ C', ∀ x, ‖R.toLinearMap x‖ ≤ C' * ‖e x‖ := ⟨C, fun x => by
    rw [show ‖e x‖ = ‖t x‖ from rfl]; exact hR x⟩
  set D0 : K →L[ℂ] E := (R.toLinearMap).extendOfNorm e with hD0def
  have hD0 : ∀ x, D0 (e x) = R x := fun x => LinearMap.extendOfNorm_eq hdense hnorm x
  set D : E →L[ℂ] E := D0.comp K.orthogonalProjectionOnto with hDdef
  have hDS : D.comp K.starProjection = D := by
    ext x
    simp only [hDdef, coe_comp, Function.comp_apply, Submodule.starProjection_apply]
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hSsa : adjoint K.starProjection = K.starProjection :=
    (isSelfAdjoint_starProjection K).adjoint_eq
  have hSD : K.starProjection.comp (adjoint D) = adjoint D := by
    have h := congrArg adjoint hDS
    rw [adjoint_comp, hSsa] at h
    exact h
  have hDt : D.comp t = R := by
    ext x
    simp only [hDdef, coe_comp, Function.comp_apply]
    have : K.orthogonalProjectionOnto (t x) = e x := by
      rw [← he x]; exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
    rw [this, hD0]
  refine ⟨(adjoint D).comp D, ?_, ?_⟩
  · rw [← comp_assoc, ← comp_assoc, hSD, comp_assoc, hDS]
  · have h := congrArg adjoint hDt
    rw [adjoint_comp, ht] at h
    rw [show t.comp (((adjoint D).comp D).comp t) = (t.comp (adjoint D)).comp (D.comp t) by
      simp only [comp_assoc], h, hDt]


open ContinuousLinearMap in
lemma douglas_pos {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (t P Cop : E →L[ℂ] E) (ht : adjoint t = t) (htt : t * t = P) (hC : 0 ≤ Cop) (lam : ℝ)
    (hle : ∀ x, (inner ℂ x (Cop x)).re ≤ lam * (inner ℂ x (P x)).re) :
    ∃ B : E →L[ℂ] E,
      ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection).comp
          (B.comp ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection)) = B ∧
      t.comp (B.comp t) = Cop := by
  set R := CFC.sqrt Cop with hRdef
  have hRsa : adjoint R = R := (CFC.sqrt_nonneg Cop).isSelfAdjoint.adjoint_eq
  have hRR : R * R = Cop := CFC.sqrt_mul_sqrt_self Cop hC
  have hbd : ∀ x, ‖R x‖ ≤ Real.sqrt (max lam 0) * ‖t x‖ := by
    intro x
    have h1 := sa_norm_sq hRsa hRR x
    have h2 := sa_norm_sq ht htt x
    have h3 : ‖R x‖ ^ 2 ≤ (Real.sqrt (max lam 0) * ‖t x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_max_right _ _), h1]
      calc (inner ℂ x (Cop x)).re ≤ lam * (inner ℂ x (P x)).re := hle x
        _ ≤ max lam 0 * (inner ℂ x (P x)).re := by
          apply mul_le_mul_of_nonneg_right (le_max_left _ _)
          rw [← h2]; exact sq_nonneg _
        _ = max lam 0 * ‖t x‖ ^ 2 := by rw [h2]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  obtain ⟨B, hB1, hB2⟩ := douglas t P R ht htt _ hbd
  refine ⟨B, hB1, ?_⟩
  rw [hB2, hRsa, ← hRR]; rfl

lemma coeff_smul {T : Type} (c : ℂ) (A : Hilbert T →L[ℂ] Hilbert T) :
    operatorCoeff (c • A) = c • operatorCoeff A := by
  funext i j; simp [operatorCoeff]

lemma coeff_rk {T : Type} (u v : Hilbert T) (i j : T) :
    operatorCoeff (rk u v) i j = u i * star (v j) := by
  rw [operatorCoeff_apply, rk_apply, inner_single_right']
  simp [mul_comm]


lemma inner_rk_self {T : Type} (u x : Hilbert T) :
    inner ℂ (rk u u x) x = ((‖inner ℂ u x‖ ^ 2 : ℝ) : ℂ) := by
  rw [rk_apply, inner_smul_left, Complex.conj_mul']
  push_cast; ring






/-! ## s3: C1 part 2, Theta(Phi sigma) = sigma -/







/-! ## s3: linearity of the trace pairing (towards C1 part 1, clauses 2-3) -/

lemma coeff_add {T : Type} (A B : Hilbert T →L[ℂ] Hilbert T) :
    operatorCoeff (A + B) = operatorCoeff A + operatorCoeff B := by
  funext i j; simp [operatorCoeff]

lemma bO_add {T : Type} {X Y : Matrix T T ℂ} (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    boundedOperator (X + Y) = boundedOperator X + boundedOperator Y :=
  bO_eq (by rw [coeff_add, coeff_bO hX, coeff_bO hY])

lemma bO_smul {T : Type} (c : ℂ) {X : Matrix T T ℂ} (hX : IsTraceClass X) :
    boundedOperator (c • X) = c • boundedOperator X :=
  bO_eq (by rw [coeff_smul, coeff_bO hX])






/-! ## s3: uniqueness of the supported dual (U1) and D(I) = I (U2 part) -/



/-! ## s4 U5: a PSD matrix with summable diagonal is trace class -/

lemma psd_diag {T : Type} {M : Matrix T T ℂ} (hM : PSDForms M) (i : T) :
    (M i i).im = 0 ∧ 0 ≤ (M i i).re := by
  have := hM {i} (fun _ => 1)
  simpa using this

lemma psd_pair {T : Type} {M : Matrix T T ℂ} (hM : PSDForms M) {i j : T} (hij : i ≠ j) (a b : ℂ) :
    (star a * M i i * a + star a * M i j * b + (star b * M j i * a + star b * M j j * b)).im = 0 ∧
    0 ≤ (star a * M i i * a + star a * M i j * b + (star b * M j i * a + star b * M j j * b)).re := by
  have h := hM {i, j} (fun k => if k = i then a else b)
  simp only [Finset.sum_pair hij, if_pos rfl, if_neg hij.symm] at h
  exact h

lemma psd_herm {T : Type} {M : Matrix T T ℂ} (hM : PSDForms M) (i j : T) : M j i = star (M i j) := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨h1, _⟩ := psd_diag hM i
    exact (Complex.conj_eq_iff_im.mpr h1).symm
  obtain ⟨h1, _⟩ := psd_pair hM hij 1 1
  obtain ⟨h2, _⟩ := psd_pair hM hij 1 Complex.I
  obtain ⟨hi, _⟩ := psd_diag hM i
  obtain ⟨hj, _⟩ := psd_diag hM j
  simp only [star_one, one_mul, mul_one, Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.star_def, Complex.conj_I, Complex.neg_re, Complex.neg_im,
    Complex.mul_re] at h1 h2
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; linarith
  · simp only [Complex.star_def, Complex.conj_im]; linarith

lemma psd_cs {T : Type} {M : Matrix T T ℂ} (hM : PSDForms M) (i j : T) :
    ‖M i j‖ ^ 2 ≤ (M i i).re * (M j j).re := by
  obtain ⟨hi, ha0⟩ := psd_diag hM i
  obtain ⟨hj, hd0⟩ := psd_diag hM j
  have hai : M i i = ((M i i).re : ℂ) := Complex.ext (by simp) (by simp [hi])
  have hdj : M j j = ((M j j).re : ℂ) := Complex.ext (by simp) (by simp [hj])
  by_cases hij : i = j
  · subst hij
    rw [hai, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp [sq]
  set b := M i j with hb
  set a := (M i i).re
  set d := (M j j).re
  set N := ‖b‖ ^ 2 with hN
  have hH : M j i = star b := psd_herm hM i j
  have hbN : b * star b = ((N : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hN]
  have key : ∀ t : ℝ, 0 ≤ a * t ^ 2 - 2 * t * N + d * N := by
    intro t
    obtain ⟨_, h⟩ := psd_pair hM hij (t : ℂ) (- star b)
    rw [hH, hai, hdj] at h
    have hE : star (t : ℂ) * (a : ℂ) * (t : ℂ) + star (t : ℂ) * b * -star b +
        (star (-star b) * star b * (t : ℂ) + star (-star b) * (d : ℂ) * -star b) =
        (((a * t ^ 2 - 2 * t * N + d * N : ℝ)) : ℂ) := by
      have hst : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
      rw [hst, star_neg, star_star]
      push_cast
      linear_combination ((d : ℂ) - 2 * (t : ℂ)) * hbN
    rw [hE, Complex.ofReal_re] at h
    exact h
  have hN0 : 0 ≤ N := sq_nonneg _
  show N ≤ a * d
  rcases lt_or_eq_of_le hd0 with hdpos | hd00
  · have := key d
    by_contra hc
    push Not at hc
    nlinarith
  · rw [← hd00, mul_zero]
    by_contra hc
    push Not at hc
    set t := N / (a + 1) with ht
    have ha1 : 0 < a + 1 := by linarith
    have htp : 0 < t := div_pos hc ha1
    have htN : t * (a + 1) = N := by rw [ht]; field_simp
    have hk := key t
    rw [← hd00, ← htN] at hk
    nlinarith [mul_pos htp htp]

lemma psd_op {T : Type} {M : Matrix T T ℂ} (hM : PSDForms M) (hd : Summable (fun i => (M i i).re)) :
    ∃ A : Hilbert T →L[ℂ] Hilbert T, operatorCoeff A = M := by
  set τ := ∑' j, (M j j).re with hτdef
  have hdn : ∀ j, 0 ≤ (M j j).re := fun j => (psd_diag hM j).2
  have hτ : 0 ≤ τ := tsum_nonneg hdn
  have hrow : ∀ i, Memℓp (fun j => M j i) 2 := by
    intro i
    rw [memℓp_two_iff']
    exact Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => psd_cs hM j i) (hd.mul_right _)
  let r : T → Hilbert T := fun i => ⟨fun j => M j i, hrow i⟩
  have hr : ∀ i, ‖r i‖ ^ 2 ≤ (M i i).re * τ := by
    intro i
    rw [← (hasSum_normSq (r i)).tsum_eq]
    calc ∑' j, ‖(r i) j‖ ^ 2 ≤ ∑' j, (M j j).re * (M i i).re :=
          Summable.tsum_le_tsum (fun j => psd_cs hM j i) (hasSum_normSq (r i)).summable (hd.mul_right _)
      _ = (M i i).re * τ := by rw [tsum_mul_right]; ring
  have hcoord : ∀ (x : Hilbert T) (i : T), ‖inner ℂ (r i) x‖ ^ 2 ≤ (M i i).re * τ * ‖x‖ ^ 2 := by
    intro x i
    calc ‖inner ℂ (r i) x‖ ^ 2 ≤ (‖r i‖ * ‖x‖) ^ 2 := by
          gcongr; exact norm_inner_le_norm _ _
      _ = ‖r i‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ (M i i).re * τ * ‖x‖ ^ 2 := by gcongr; exact hr i
  have hmem : ∀ x : Hilbert T, Memℓp (fun i => inner ℂ (r i) x) 2 := by
    intro x
    rw [memℓp_two_iff']
    exact Summable.of_nonneg_of_le (fun i => sq_nonneg _) (hcoord x) ((hd.mul_right τ).mul_right _)
  let f : Hilbert T →ₗ[ℂ] Hilbert T :=
    { toFun := fun x => ⟨fun i => inner ℂ (r i) x, hmem x⟩
      map_add' := fun x y => lp.ext (funext fun i => by
        show inner ℂ (r i) (x + y) = inner ℂ (r i) x + inner ℂ (r i) y
        exact inner_add_right _ _ _)
      map_smul' := fun c x => lp.ext (funext fun i => by
        show inner ℂ (r i) (c • x) = c • inner ℂ (r i) x
        rw [inner_smul_right, smul_eq_mul]) }
  have hfx : ∀ x i, (f x) i = inner ℂ (r i) x := fun _ _ => rfl
  have hbound : ∀ x, ‖f x‖ ≤ τ * ‖x‖ := by
    intro x
    have h1 : ‖f x‖ ^ 2 ≤ (τ * ‖x‖) ^ 2 := by
      rw [← (hasSum_normSq (f x)).tsum_eq]
      calc ∑' i, ‖(f x) i‖ ^ 2 ≤ ∑' i, (M i i).re * τ * ‖x‖ ^ 2 :=
            Summable.tsum_le_tsum (fun i => by rw [hfx]; exact hcoord x i)
              (hasSum_normSq _).summable ((hd.mul_right τ).mul_right _)
        _ = (τ * ‖x‖) ^ 2 := by rw [tsum_mul_right, tsum_mul_right]; ring
    nlinarith [norm_nonneg (f x), mul_nonneg hτ (norm_nonneg x)]
  refine ⟨f.mkContinuous τ hbound, ?_⟩
  funext i j
  rw [operatorCoeff_apply, LinearMap.mkContinuous_apply, hfx, inner_single_right']
  show star (M j i) = M i j
  rw [psd_herm hM j i]

lemma pos_op {T : Type} {X : Matrix T T ℂ} (S : Hilbert T →L[ℂ] Hilbert T) (hS : operatorCoeff S = X)
    (hX : PSDForms X) (y : Hilbert T) : (inner ℂ y (S y)).im = 0 ∧ 0 ≤ (inner ℂ y (S y)).re := by
  let Q : Set ℂ := {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}
  have hQ : IsClosed Q :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hcont : Continuous (fun x : Hilbert T => inner ℂ x (S x)) :=
    continuous_id.inner S.continuous
  have h0 : Filter.Tendsto (fun s : Finset T => ∑ j ∈ s, y j • (lp.single 2 j (1:ℂ) : Hilbert T))
      Filter.atTop (nhds y) := hasSum_basis y
  have htend := (hcont.tendsto y).comp h0
  refine hQ.mem_of_tendsto htend (Filter.Eventually.of_forall (fun s => ?_))
  have := hX s (fun t => y t)
  show (inner ℂ (∑ j ∈ s, y j • (lp.single 2 j (1:ℂ) : Hilbert T))
      (S (∑ j ∈ s, y j • (lp.single 2 j (1:ℂ) : Hilbert T)))) ∈ Q
  have hf := form_eq S s id (fun t => y t)
  rw [hS] at hf
  simp only [id] at hf
  rw [← hf]
  exact this

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- U5: a matrix with positive finite forms and summable diagonal is trace class. -/
theorem psd_tc {T : Type} [Countable T] {M : Matrix T T ℂ} (hM : PSDForms M)
    (hd : Summable (fun i => (M i i).re)) :
    IsTraceClass M ∧ traceSize M ≤ ENNReal.ofReal (∑' i, (M i i).re) := by
  obtain ⟨A, hA⟩ := psd_op hM hd
  have hpos : 0 ≤ A := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
    intro x
    obtain ⟨him, hre⟩ := pos_op A hA hM x
    have hz : inner ℂ (A x) x = inner ℂ x (A x) := by
      rw [← inner_conj_symm]; exact Complex.conj_eq_iff_im.mpr him
    rw [hz]
    refine ⟨?_, by simpa using hre⟩
    apply Complex.ext <;> simp [him]
  obtain ⟨hR, hRR⟩ := psr_facts A hpos
  set R := positiveSquareRoot A
  let w : T → Hilbert T := fun k => R (bvec k)
  have hw : ∀ k, ‖w k‖ * ‖w k‖ = (M k k).re := by
    intro k
    rw [← sq, sa_norm_sq hR hRR, inner_bvec_left, ← hA, operatorCoeff_apply]
    rfl
  have hcoef : ∀ a b, HasSum (fun k => w k a * star (w k b)) (M a b) := by
    intro a b
    have hw' : ∀ c k, w k c = star ((R (bvec c)) k) := by
      intro c k
      show (R (bvec k)) c = _
      rw [coord_eq_inner, sa_swap hR]
      exact inner_single_right' _ _
    have hwa : ∀ k, w k a = star ((R (bvec a)) k) := hw' a
    have hwb : ∀ k, star (w k b) = (R (bvec b)) k := by
      intro k
      rw [hw' b k, star_star]
    have h := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : T => ℂ) (R (bvec a)) (R (bvec b))
    have hval : inner ℂ (R (bvec a)) (R (bvec b)) = M a b := by
      rw [← sa_swap hR, show R (R (bvec b)) = (R * R) (bvec b) from rfl, hRR, inner_bvec_left,
        ← hA, operatorCoeff_apply]
      rfl
    rw [hval] at h
    have heq : (fun k => w k a * star (w k b)) =
        fun k => inner ℂ ((R (bvec a)) k) ((R (bvec b)) k) := by
      funext k
      rw [hwa, hwb]
      simp [RCLike.inner_apply, mul_comm]
    rw [heq]
    exact h
  have hs : Summable (fun k => ‖w k‖ * ‖w k‖) := by simp_rw [hw]; exact hd
  have := traceSize_le_of_countable w w hs hcoef
  simp_rw [hw] at this
  exact this


/-! ## s4: positivity of trace pairings -/

/-! ## s4 U3: complete positivity pieces -/









lemma bO_zero {T : Type} : boundedOperator (0 : Matrix T T ℂ) = 0 :=
  bO_eq (by funext i j; simp [operatorCoeff])



/-! ## s5: pairing through a rank-one expansion over any index (U3e core) -/









/-! ## s5: U3b, positivity of the supported dual on rank-one families -/










/-! ## s6: U4 normality of the Petz dual -/

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
lemma dens_form {T : Type} (rho : State T) (g : Hilbert T) :
    (inner ℂ g (boundedOperator rho.coefficients g)).im = 0 ∧
    0 ≤ (inner ℂ g (boundedOperator rho.coefficients g)).re ∧
    (inner ℂ g (boundedOperator rho.coefficients g)).re ≤ ‖g‖ ^ 2 := by
  obtain ⟨hr, hrr, hsum⟩ := sqrt_state rho
  set r := positiveSquareRoot (boundedOperator rho.coefficients) with hrdef
  have h1 : inner ℂ g (boundedOperator rho.coefficients g) = ((‖r g‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hrr, ContinuousLinearMap.mul_apply, sa_swap hr, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  have h2 : ‖r g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
    have hn := hasSum_normSq (r g)
    have hb : HasSum (fun k => ‖r (bvec k)‖ ^ 2 * ‖g‖ ^ 2) (1 * ‖g‖ ^ 2) := hsum.mul_right _
    refine le_of_le_of_eq (hasSum_le (fun k => ?_) hn hb) (one_mul _)
    rw [coord_eq_inner, sa_swap hr, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  rw [h1]
  simp only [Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨trivial, sq_nonneg _, h2⟩



lemma tc_fsum {T ι : Type} (F : Finset ι) (Y : ι → Matrix T T ℂ) (hY : ∀ i, IsTraceClass (Y i)) :
    IsTraceClass (∑ i ∈ F, Y i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (tc_zero : IsTraceClass (0 : Matrix T T ℂ))
  | insert a F ha ih => rw [Finset.sum_insert ha]; exact tc_add (hY a) ih

lemma bO_fsum {T ι : Type} (F : Finset ι) (Y : ι → Matrix T T ℂ) (hY : ∀ i, IsTraceClass (Y i)) :
    boundedOperator (∑ i ∈ F, Y i) = ∑ i ∈ F, boundedOperator (Y i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (bO_zero : boundedOperator (0 : Matrix T T ℂ) = 0)
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, bO_add (hY a) (tc_fsum F Y hY), ih]



























end P45Petz


section C3Part

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators ENNReal ComplexOrder Topology Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace P45C3

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsDensity IsTraceClassChannel NuclearExpansion tensorApply)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open P45Petz






/-! ### Padding a finite block into `I` -/

/-! ### The finite maps Γ_{s,t} Z = (Ψ (pad Z))_t -/

/-! ### Two-colour lift of a density and convergence of truncations -/

end P45C3

end

end C3Part

section N0Part

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace P45N0

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity IsTraceClassChannel)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats finiteRelativeEntropy)
open QAlgorithms.Papers.Independent.Frontier18.P18 (ReversibleOn)
open P45Petz P45C3

variable {I L : Type}

lemma dens_psd (rho : State I) : PSDForms rho.coefficients := rho.density.2.1

lemma dens_diag_hasSum' (rho : State I) : HasSum (fun a => (rho.coefficients a a).re) 1 := by
  have h := rho.density.2.2.1.hasSum
  rwa [rho.density.2.2.2] at h

lemma psd_coef_le {T : Type} {M : Matrix T T ℂ} (hM : PSDForms M) {t : ℝ}
    (hd : HasSum (fun a => (M a a).re) t) (a b : T) : ‖M a b‖ ≤ t := by
  have hle : ∀ c, (M c c).re ≤ t := fun c => le_hasSum hd c (fun j _ => (psd_diag hM j).2)
  have h := psd_cs hM a b
  have ht : 0 ≤ t := (psd_diag hM a).2.trans (hle a)
  have h1 : (M a a).re * (M b b).re ≤ t * t :=
    mul_le_mul (hle a) (hle b) (psd_diag hM b).2 ht
  nlinarith [norm_nonneg (M a b)]

lemma dens_coef_le (rho : State I) (a b : I) : ‖rho.coefficients a b‖ ≤ 1 :=
  psd_coef_le (dens_psd rho) (dens_diag_hasSum' rho) a b

/-- Weighted coefficient barycenter. -/
def wm (w : L → ℝ) (rho : L → State I) : Matrix I I ℂ :=
  fun a b => ∑' j, (w j : ℂ) * (rho j).coefficients a b

lemma wm_summable {w : L → ℝ} (hw : Summable w) (rho : L → State I) (a b : I) :
    Summable (fun j => (w j : ℂ) * (rho j).coefficients a b) := by
  refine Summable.of_norm_bounded hw.abs (fun j => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (dens_coef_le _ a b)

lemma wm_form_hasSum {w : L → ℝ} (hw : Summable w) (rho : L → State I) (s : Finset I)
    (z : I → ℂ) :
    HasSum (fun j => (w j : ℂ) * ∑ a ∈ s, ∑ b ∈ s, star (z a) * (rho j).coefficients a b * z b)
      (∑ a ∈ s, ∑ b ∈ s, star (z a) * wm w rho a b * z b) := by
  have h : ∀ a b, HasSum (fun j => star (z a) * ((w j : ℂ) * (rho j).coefficients a b) * z b)
      (star (z a) * wm w rho a b * z b) :=
    fun a b => (((wm_summable hw rho a b).hasSum).mul_left (star (z a))).mul_right (z b)
  have h2 : HasSum (fun j => ∑ a ∈ s, ∑ b ∈ s,
      star (z a) * ((w j : ℂ) * (rho j).coefficients a b) * z b)
      (∑ a ∈ s, ∑ b ∈ s, star (z a) * wm w rho a b * z b) :=
    hasSum_sum (fun a _ => hasSum_sum (fun b _ => h a b))
  convert h2 using 1
  funext j
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

lemma wm_psd {w : L → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w) (rho : L → State I) :
    PSDForms (wm w rho) := by
  intro s z
  have h := wm_form_hasSum hw rho s z
  have hre := Complex.reCLM.hasSum h
  have him := Complex.imCLM.hasSum h
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
  constructor
  · refine him.unique ?_
    convert (hasSum_zero : HasSum (fun _ : L => (0 : ℝ)) 0) using 1
    funext j
    have := (dens_psd (rho j) s z).1
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, this, mul_zero, zero_mul,
      add_zero]
  · refine hre.nonneg (fun j => ?_)
    have := dens_psd (rho j) s z
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (hw0 j) this.2

lemma wm_diag_hasSum {w : L → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w) (rho : L → State I) :
    HasSum (fun a => (wm w rho a a).re) (∑' j, w j) := by
  let g : L × I → ℝ := fun p => w p.1 * ((rho p.1).coefficients p.2 p.2).re
  have hg : ∀ p, 0 ≤ g p := fun p => mul_nonneg (hw0 _) (psd_diag (dens_psd _) _).2
  have ha : ∀ j, HasSum (fun a => g (j, a)) (w j) := by
    intro j
    simpa [g] using (dens_diag_hasSum' (rho j)).mul_left (w j)
  have hb : ∀ a, HasSum (fun j => g (j, a)) ((wm w rho a a).re) := by
    intro a
    have h := Complex.reCLM.hasSum (wm_summable hw rho a a).hasSum
    simpa [g, wm, Complex.mul_re] using h
  exact dsum_swap g hg ha hw.hasSum hb

lemma wm_tc [Countable I] {w : L → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w)
    (rho : L → State I) : IsTraceClass (wm w rho) :=
  (psd_tc (wm_psd hw0 hw rho) (wm_diag_hasSum hw0 hw rho).summable).1

lemma wm_density [Countable I] {w : L → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw : HasSum w 1)
    (rho : L → State I) : IsDensity (wm w rho) := by
  have hd := wm_diag_hasSum hw0 hw.summable rho
  rw [hw.tsum_eq] at hd
  exact ⟨wm_tc hw0 hw.summable rho, wm_psd hw0 hw.summable rho, hd.summable, hd.tsum_eq⟩

lemma compl_hasSum {w : L → ℝ} (hw : Summable w) (F : Finset L) :
    HasSum (fun j => if j ∈ F then 0 else w j) (∑' j, w j - ∑ j ∈ F, w j) := by
  have h1 : HasSum (fun j => if j ∈ F then w j else 0) (∑ j ∈ F, if j ∈ F then w j else 0) :=
    hasSum_sum_of_ne_finset_zero (fun j hj => if_neg hj)
  rw [Finset.sum_congr rfl (fun j hj => if_pos hj)] at h1
  have hfun : (fun j => if j ∈ F then 0 else w j) = fun j => w j - (if j ∈ F then w j else 0) := by
    funext j; split_ifs <;> simp
  rw [hfun]; exact hw.hasSum.sub h1

lemma wm_split {w : L → ℝ} (hw : Summable w) (rho : L → State I) (F : Finset L) :
    wm w rho = (∑ j ∈ F, ((w j : ℂ) • (rho j).coefficients)) +
      wm (fun j => if j ∈ F then 0 else w j) rho := by
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, wm]
  have h1 : HasSum (fun j => if j ∈ F then (w j : ℂ) * (rho j).coefficients a b else 0)
      (∑ j ∈ F, if j ∈ F then (w j : ℂ) * (rho j).coefficients a b else 0) :=
    hasSum_sum_of_ne_finset_zero (fun j hj => if_neg hj)
  rw [Finset.sum_congr rfl (fun j hj => if_pos hj)] at h1
  have h3 := (wm_summable hw rho a b).hasSum.sub h1
  have : (fun j => (((if j ∈ F then 0 else w j : ℝ)) : ℂ) * (rho j).coefficients a b) =
      fun j => (w j : ℂ) * (rho j).coefficients a b -
        (if j ∈ F then (w j : ℂ) * (rho j).coefficients a b else 0) := by
    funext j; split_ifs <;> simp
  rw [this, h3.tsum_eq]; ring





end P45N0

end

end N0Part
section C4aPart

set_option autoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace

/-! C4 infrastructure for 0d372677 (Petz equality). K-a: the Parseval identity behind the
resolvent variational form Q_t(rho, sigma) = sup_W [2 Re Tr(rho W) - Tr(sigma W W*) - t Tr(rho W* W)].
Generic Hilbert space with two Hilbert bases (eigenbases of rho and sigma in the application). -/

namespace P45C4

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type}











section Trunc

attribute [local instance] Classical.propDecidable

variable (e : HilbertBasis ι ℂ E) (f : HilbertBasis κ ℂ E) (r : ι → ℝ) (s : κ → ℝ) (t : ℝ)

/-- The value of the resolvent variational problem at W (in eigen coordinates). -/
def val (W : E →L[ℂ] E) : ℝ :=
  2 * (∑' i, r i * (⟪e i, W (e i)⟫_ℂ).re) - ∑' j, s j * ‖(ContinuousLinearMap.adjoint W) (f j)‖ ^ 2
    - t * ∑' i, r i * ‖W (e i)‖ ^ 2





variable {r s t}






end Trunc

section Compact





end Compact

section Eigen




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

/-! ## C4 bridge: eigen data of a State and the trace pairing in eigen coordinates (s12) -/
section C4Bridge

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace P45C4B

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open P45Petz P45C4
open scoped InnerProductSpace







section Dual

variable {I J : Type}




















/-! ### Duality Tr(Phi(X) W) = Tr(X Phi*(W)) on all trace class (normality via positive pieces) -/











end Dual

end P45C4B

end

end C4Bridge

section N1Part

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace P45N1
noncomputable local instance (priority := 1100) scH_nacg_6 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_6 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_6 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_6 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_6 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_6 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_6 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scC_acm_6 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_mod_6 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Module ℂ (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_6 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_6 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
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

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity IsTraceClassChannel)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)
open P45Petz P45N0


section GenN1b
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


lemma sp_adj (K : Submodule ℂ E) [K.HasOrthogonalProjection] :
    ContinuousLinearMap.adjoint K.starProjection = K.starProjection := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact isSelfAdjoint_starProjection _

lemma nonneg_adj {C : E →L[ℂ] E} (hC : 0 ≤ C) : ContinuousLinearMap.adjoint C = C := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive C).mp hC).isSelfAdjoint


/-- Symmetrised Douglas factorisation. -/
lemma douglas_sym (t P C : E →L[ℂ] E) (ht : ContinuousLinearMap.adjoint t = t) (htt : t * t = P)
    (hC : 0 ≤ C) (hle : ∀ x, (inner ℂ x (C x)).re ≤ (inner ℂ x (P x)).re) :
    ∃ B : E →L[ℂ] E,
      ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection).comp
          (B.comp ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection)) = B ∧
      t.comp (B.comp t) = C ∧ ContinuousLinearMap.adjoint B = B := by
  obtain ⟨B, hS, hB⟩ := douglas_pos t P C ht htt hC 1 (by simpa using hle)
  set S := (LinearMap.range P.toLinearMap).topologicalClosure.starProjection with hSdef
  have hSa : ContinuousLinearMap.adjoint S = S := sp_adj _
  have hCa := nonneg_adj hC
  have hSB' : S.comp ((ContinuousLinearMap.adjoint B).comp S) = ContinuousLinearMap.adjoint B := by
    have := congrArg ContinuousLinearMap.adjoint hS
    simpa only [ContinuousLinearMap.adjoint_comp, hSa, ContinuousLinearMap.comp_assoc] using this
  have htB' : t.comp ((ContinuousLinearMap.adjoint B).comp t) = C := by
    have := congrArg ContinuousLinearMap.adjoint hB
    simpa only [ContinuousLinearMap.adjoint_comp, ht, hCa, ContinuousLinearMap.comp_assoc] using this
  refine ⟨(1 / 2 : ℂ) • (B + ContinuousLinearMap.adjoint B), ?_, ?_, ?_⟩
  · simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hS, hSB']
  · simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hB, htB']
    rw [← two_smul ℂ C, smul_smul]; norm_num
  · rw [map_smulₛₗ, map_add, ContinuousLinearMap.adjoint_adjoint, add_comm]
    congr 1
    apply Complex.ext <;> simp



end GenN1b

/-- Form of a sub-normalised mixture of states lies in `[0, (∑ w) ‖y‖²]`. -/
lemma wm_form_tail {J L : Type} [Countable J] {w : L → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w)
    (rho : L → State J) (y : Hilbert J) :
    0 ≤ (inner ℂ y (boundedOperator (wm w rho) y)).re ∧
    (inner ℂ y (boundedOperator (wm w rho) y)).re ≤ (∑' j, w j) * ‖y‖ ^ 2 := by
  rcases (tsum_nonneg hw0).eq_or_lt with h0 | hpos
  · have hz : w = 0 := (hasSum_zero_iff_of_nonneg hw0).mp (h0 ▸ hw.hasSum)
    have hm : wm w rho = 0 := by
      funext a b; simp [wm, hz]
    rw [hm, bO_zero, ← h0]
    simp
  · set c := ∑' j, w j with hc
    have hw1 : HasSum (fun j => w j / c) 1 := by
      have := hw.hasSum.div_const c
      rwa [div_self hpos.ne'] at this
    have hd := wm_density (fun j => div_nonneg (hw0 j) hpos.le) hw1 rho
    have heq : wm w rho = (c : ℂ) • wm (fun j => w j / c) rho := by
      funext a b
      simp only [wm, Matrix.smul_apply, smul_eq_mul]
      rw [← tsum_mul_left]
      refine tsum_congr (fun j => ?_)
      push_cast
      field_simp
    have hf := dens_form (⟨wm (fun j => w j / c) rho, hd⟩ : State J) y
    simp only at hf
    rw [heq, bO_smul _ hd.1, ContinuousLinearMap.smul_apply, inner_smul_right,
      Complex.re_ofReal_mul]
    exact ⟨mul_nonneg hpos.le hf.2.1, mul_le_mul_of_nonneg_left hf.2.2 hpos.le⟩

/-- KEY: the quadratic form of a mixture is the mixture of the quadratic forms. -/
lemma wm_form_hasSum' {J L : Type} [Countable J] {w : L → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : Summable w) (rho : L → State J) (y : Hilbert J) :
    HasSum (fun j => w j * (inner ℂ y (boundedOperator (rho j).coefficients y)).re)
      (inner ℂ y (boundedOperator (wm w rho) y)).re := by
  set wF : Finset L → L → ℝ := fun F j => if j ∈ F then 0 else w j with hwF
  have hwF0 : ∀ F j, 0 ≤ wF F j := fun F j => by
    simp only [hwF]; split_ifs
    · exact le_rfl
    · exact hw0 j
  have hwFs : ∀ F, HasSum (wF F) (∑' j, w j - ∑ j ∈ F, w j) := fun F => compl_hasSum hw F
  have hsplit : ∀ F : Finset L, (inner ℂ y (boundedOperator (wm w rho) y)).re =
      ∑ j ∈ F, w j * (inner ℂ y (boundedOperator (rho j).coefficients y)).re +
      (inner ℂ y (boundedOperator (wm (wF F) rho) y)).re := by
    intro F
    have htc : ∀ j, IsTraceClass ((w j : ℂ) • (rho j).coefficients) :=
      fun j => tc_smul _ (rho j).density.1
    rw [wm_split hw rho F, bO_add (tc_fsum F _ htc) (wm_tc (hwF0 F) (hwFs F).summable rho),
      bO_fsum F _ htc]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, inner_add_right,
      inner_sum, Complex.add_re, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [bO_smul _ (rho j).density.1, ContinuousLinearMap.smul_apply, inner_smul_right,
      Complex.re_ofReal_mul]
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ F : Finset L, ‖∑ j ∈ F, w j * (inner ℂ y (boundedOperator (rho j).coefficients y)).re -
      (inner ℂ y (boundedOperator (wm w rho) y)).re‖ ≤ (∑' j, w j - ∑ j ∈ F, w j) * ‖y‖ ^ 2 := by
    intro F
    have h1 := wm_form_tail (hwF0 F) (hwFs F).summable rho y
    rw [(hwFs F).tsum_eq] at h1
    rw [hsplit F, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2]
  refine squeeze_zero (fun F => norm_nonneg _) hb ?_
  have hw2 : Tendsto (fun F : Finset L => ∑ j ∈ F, w j) atTop (𝓝 (∑' j, w j)) := hw.hasSum
  simpa using ((tendsto_const_nhds (x := ∑' j, w j)).sub hw2).mul_const (‖y‖ ^ 2)










lemma pos_form_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hA : A.IsPositive) (x : E) (h : (inner ℂ x (A x)).re = 0) : A x = 0 := by
  have hA0 : 0 ≤ A := (ContinuousLinearMap.nonneg_iff_isPositive A).mpr hA
  obtain ⟨hr, hrr⟩ := psr_facts A hA0
  have h1 := sa_norm_sq hr hrr x
  rw [h] at h1
  have h2 : positiveSquareRoot A x = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)
  rw [← hrr, ContinuousLinearMap.mul_apply, h2, map_zero]

/-- N1a(i): the barycenter of a complete family with positive weights is faithful. -/
theorem faithful {I L : Type} [Countable I] (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) {pi : L → ℝ} (hpi : PositiveLaw pi) (sigma : State I)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b)
    (x : Hilbert I) (hx : boundedOperator sigma.coefficients x = 0) : x = 0 := by
  have hpi0 : ∀ j, 0 ≤ pi j := fun j => (hpi.1 j).le
  have hs : sigma.coefficients = wm pi rho := hbar
  have hsum := wm_form_hasSum' hpi0 hpi.2.summable rho x
  rw [← hs, hx, inner_zero_right, Complex.zero_re] at hsum
  have hnn : ∀ j, 0 ≤ pi j * (inner ℂ x (boundedOperator (rho j).coefficients x)).re := fun j =>
    mul_nonneg (hpi0 j) ((bO_pos (rho j)).re_inner_nonneg_right x)
  have hz := (hasSum_zero_iff_of_nonneg hnn).mp hsum
  have hj : ∀ j, boundedOperator (rho j).coefficients x = 0 := fun j => by
    have h1 := congrFun hz j
    simp only [Pi.zero_apply, mul_eq_zero, (hpi.1 j).ne', false_or] at h1
    exact pos_form_zero _ (bO_pos (rho j)) x h1
  have hgen : Submodule.span ℂ {v | ∃ r ∈ Set.range rho, ∃ w, boundedOperator r.coefficients w = v}
      ≤ (ℂ ∙ x)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨r, ⟨j, rfl⟩, w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [inner_smul_left, ← ContinuousLinearMap.adjoint_inner_left,
      nonneg_adj ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (bO_pos (rho j))), hj j,
      inner_zero_left, mul_zero]
  have hcl := Submodule.topologicalClosure_minimal _ hgen (Submodule.isClosed_orthogonal _)
  have htop : (Submodule.span ℂ {v | ∃ r ∈ Set.range rho, ∃ w,
      boundedOperator r.coefficients w = v}).topologicalClosure = ⊤ := hC
  rw [htop] at hcl
  have hx' : x ∈ (ℂ ∙ x)ᗮ := hcl Submodule.mem_top
  rw [Submodule.mem_orthogonal] at hx'
  exact inner_self_eq_zero.mp (hx' x (Submodule.mem_span_singleton_self x))




end P45N1

end

end N1Part

section N1Rank
set_option autoImplicit false

noncomputable section

namespace P45N1R


end P45N1R
end
end N1Rank

section N1Asm

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace P45N1A
noncomputable local instance (priority := 1100) scH_nacg_8 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_8 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_8 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_8 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_8 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_8 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_am_8 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_8 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_8 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_8 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_algR_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_algC_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℂ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_t2_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : T2Space (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_po_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : PartialOrder (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cstar_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : CStarAlgebra (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_sor_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_nsc_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cfcR_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_ncfcR_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_istR_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_smcR_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_star_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_tr_8 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsTopologicalRing (E →L[ℂ] E) := inferInstance

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)
open P45Petz P45N0 P45N1

/-- The square root of a faithful barycenter is injective with dense range. -/
lemma sqrt_inj_dense {I L : Type} [Countable I] (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) {pi : L → ℝ} (hpi : PositiveLaw pi) (sigma : State I)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    Function.Injective (positiveSquareRoot (boundedOperator sigma.coefficients)) ∧
    DenseRange (positiveSquareRoot (boundedOperator sigma.coefficients)) := by
  have hfaith := faithful rho hC hpi sigma hbar
  obtain ⟨hs, hss, _⟩ := sqrt_state sigma
  set s := positiveSquareRoot (boundedOperator sigma.coefficients) with hsdef
  have hinj : Function.Injective s := by
    refine (injective_iff_map_eq_zero s).mpr ?_
    intro v hv
    exact hfaith v (by rw [← hss, ContinuousLinearMap.mul_apply, hv, map_zero])
  refine ⟨hinj, ?_⟩
  have hRperp : (LinearMap.range s.toLinearMap)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    apply hinj
    rw [map_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
    have h := Submodule.inner_right_of_mem_orthogonal
      (LinearMap.mem_range_self s.toLinearMap (s v)) hv
    rw [sa_swap hs]
    exact h
  have hcl : (LinearMap.range s.toLinearMap).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hRperp, Submodule.bot_orthogonal_eq_top]
  have hD := Submodule.dense_iff_topologicalClosure_eq_top.mpr hcl
  simpa [DenseRange, LinearMap.coe_range] using hD


end P45N1A

end

end N1Asm

section N2A

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace P45N2
noncomputable local instance (priority := 1100) scH_nacg_9 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_9 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_9 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_9 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_9 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_9 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_9 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_am_9 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_9 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_9 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_9 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_algR_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_algC_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Algebra ℂ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_t2_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : T2Space (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_po_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : PartialOrder (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cstar_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : CStarAlgebra (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_sor_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_nsc_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_cfcR_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_ncfcR_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance
noncomputable local instance (priority := 1100) scA_istR_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_smcR_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_star_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] : StarRing (E →L[ℂ] E) := inferInstance
noncomputable local instance (priority := 1100) scA_tr_9 {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsTopologicalRing (E →L[ℂ] E) := inferInstance

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator IsParsevalFrame)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)
open P45Petz P45N0 P45N1 P45N1A

lemma bO_rankOne {T : Type} (u : Hilbert T) : boundedOperator (rankOne u) = rk u u :=
  bO_eq (by funext i j; rw [coeff_rk]; rfl)

/-- `inverseRootImage` returns a preimage when one exists and the root is injective. -/
lemma inv_root_spec {I : Type} (X : Matrix I I ℂ) (y u : Hilbert I)
    (hu : positiveSquareRoot (boundedOperator X) u = y)
    (hinj : Function.Injective (positiveSquareRoot (boundedOperator X))) :
    positiveSquareRoot (boundedOperator X) (inverseRootImage X y) = y := by
  have hker : LinearMap.ker (positiveSquareRoot (boundedOperator X)).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hex : ∃ u : Hilbert I, positiveSquareRoot (boundedOperator X) u = y ∧
      u ∈ (LinearMap.ker (positiveSquareRoot (boundedOperator X)).toLinearMap)ᗮ :=
    ⟨u, hu, by rw [hker, Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top⟩
  unfold inverseRootImage
  rw [dif_pos hex]
  exact hex.choose_spec.1

/-- The coordinate vector of a Bessel family. -/
def anaVec {I L : Type} (w : L → Hilbert I) (x : Hilbert I)
    (hs : Summable (fun i => ‖inner ℂ (w i) x‖ ^ 2)) : Hilbert L :=
  ⟨fun i => inner ℂ (w i) x, (memℓp_two_iff' _).mpr hs⟩

lemma anaVec_norm_le {I L : Type} (w : L → Hilbert I)
    (hb : ∀ x, ∀ F : Finset L, ∑ i ∈ F, ‖inner ℂ (w i) x‖ ^ 2 ≤ ‖x‖ ^ 2) (x : Hilbert I) :
    ‖anaVec w x (summable_of_sum_le (fun i => by positivity) (hb x))‖ ≤ ‖x‖ := by
  have h1 := hasSum_normSq (anaVec w x (summable_of_sum_le (fun i => by positivity) (hb x)))
  have h2 : ‖anaVec w x (summable_of_sum_le (fun i => by positivity) (hb x))‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← h1.tsum_eq]
    exact h1.summable.tsum_le_of_sum_le (hb x)
  nlinarith [norm_nonneg x, norm_nonneg (anaVec w x
    (summable_of_sum_le (fun i => by positivity) (hb x)))]

/-- The analysis operator of a Bessel family. -/
def anaOp {I L : Type} (w : L → Hilbert I)
    (hb : ∀ x, ∀ F : Finset L, ∑ i ∈ F, ‖inner ℂ (w i) x‖ ^ 2 ≤ ‖x‖ ^ 2) :
    Hilbert I →L[ℂ] Hilbert L :=
  LinearMap.mkContinuous
    { toFun := fun x => anaVec w x (summable_of_sum_le (fun i => by positivity) (hb x))
      map_add' := fun x y => by
        ext i
        change inner ℂ (w i) (x + y) = inner ℂ (w i) x + inner ℂ (w i) y
        exact inner_add_right _ _ _
      map_smul' := fun c x => by
        ext i
        change inner ℂ (w i) (c • x) = c * inner ℂ (w i) x
        exact inner_smul_right _ _ _ }
    1 (fun x => by rw [one_mul]; exact anaVec_norm_le w hb x)


/-- A Bessel family whose analysis operator is isometric is a Parseval frame. -/
lemma parseval_of_iso {I L : Type} (w : L → Hilbert I)
    (hb : ∀ x, ∀ F : Finset L, ∑ i ∈ F, ‖inner ℂ (w i) x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hiso : ∀ x, ‖anaOp w hb x‖ = ‖x‖) : IsParsevalFrame w := by
  set A := anaOp w hb with hAdef
  have hAA : ContinuousLinearMap.adjoint A ∘L A = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self A).mp hiso
  have hAst : ∀ (i : L) (c : ℂ), ContinuousLinearMap.adjoint A (lp.single 2 i c) = c • w i := by
    intro i c
    refine ext_inner_left ℂ fun z => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_single_right, inner_smul_right]
    change inner ℂ (inner ℂ (w i) z) c = c * inner ℂ z (w i)
    rw [← inner_conj_symm z (w i)]
    simp only [RCLike.inner_apply]
    try ring
  intro x
  have h := (lp.hasSum_single (p := 2) (by simp) (A x)).mapL (ContinuousLinearMap.adjoint A)
  have hx : ContinuousLinearMap.adjoint A (A x) = x := by
    have := congrArg (fun T : Hilbert I →L[ℂ] Hilbert I => T x) hAA
    simpa using this
  rw [hx] at h
  have hf : (fun i => ContinuousLinearMap.adjoint A (lp.single 2 i ((A x : L → ℂ) i))) =
      fun i => inner ℂ (w i) x • w i := by
    funext i
    rw [hAst]
    rfl
  rw [hf] at h
  exact h

/-- N2a: the whitened vectors of a complete pure family exist (exact inverse equation)
and form a Parseval frame. -/
theorem n2a {I L : Type} [Countable I] (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) (v : L → Hilbert I)
    (hv : ∀ i, ‖v i‖ = 1 ∧ (rho i).coefficients = rankOne (v i))
    (pi : L → ℝ) (sigma : State I) (hpi : PositiveLaw pi)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    (∀ i, positiveSquareRoot (boundedOperator (vectorAverage pi v)) (whitenedVector pi v i) =
      (Real.sqrt (pi i) : ℂ) • v i) ∧ IsParsevalFrame (whitenedVector pi v) := by
  have hpi0 : ∀ j, 0 ≤ pi j := fun j => (hpi.1 j).le
  have hva : vectorAverage pi v = sigma.coefficients := by
    rw [hbar]
    funext a b
    simp only [vectorAverage, (hv _).2]
  have hs' : wm pi rho = sigma.coefficients := hbar.symm
  obtain ⟨hinj, hdense⟩ := sqrt_inj_dense rho hC hpi sigma hbar
  obtain ⟨hsa, hss, _⟩ := sqrt_state sigma
  set s := positiveSquareRoot (boundedOperator sigma.coefficients) with hsdef
  have hform : ∀ y, HasSum (fun j => pi j * (inner ℂ y (boundedOperator (rho j).coefficients y)).re)
      (inner ℂ y (boundedOperator sigma.coefficients y)).re := by
    intro y
    have h := wm_form_hasSum' hpi0 hpi.2.summable rho y
    rw [hs'] at h
    exact h
  -- preimages of sqrt(pi_i) v_i under s (Douglas)
  have hpre : ∀ i, ∃ u, s u = (Real.sqrt (pi i) : ℂ) • v i := by
    intro i
    have hC0 : 0 ≤ (pi i : ℂ) • boundedOperator (rho i).coefficients := by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      exact (bO_pos (rho i)).smul_of_nonneg (by exact_mod_cast (hpi.1 i).le)
    have hle : ∀ x, (inner ℂ x (((pi i : ℂ) • boundedOperator (rho i).coefficients) x)).re ≤
        (inner ℂ x (boundedOperator sigma.coefficients x)).re := by
      intro x
      have e : (inner ℂ x (((pi i : ℂ) • boundedOperator (rho i).coefficients) x)).re =
          pi i * (inner ℂ x (boundedOperator (rho i).coefficients x)).re := by
        simp only [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]
      rw [e]
      exact le_hasSum (hform x) i (fun j _ =>
        mul_nonneg (hpi0 j) ((bO_pos (rho j)).re_inner_nonneg_right x))
    obtain ⟨B, _, hBt, _⟩ := douglas_sym s _ _ hsa hss hC0 hle
    have hBv : s (B (s (v i))) = (pi i : ℂ) • v i := by
      have := congrArg (fun T : Hilbert I →L[ℂ] Hilbert I => T (v i)) hBt
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this, ContinuousLinearMap.smul_apply, (hv i).2, bO_rankOne, rk_apply,
        inner_self_eq_norm_sq_to_K, (hv i).1]
      simp
    have hsq0 : (Real.sqrt (pi i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hpi.1 i)).ne'
    refine ⟨((Real.sqrt (pi i) : ℂ))⁻¹ • B (s (v i)), ?_⟩
    rw [map_smul, hBv, smul_smul]
    congr 1
    have hsq : (pi i : ℂ) = (Real.sqrt (pi i) : ℂ) * (Real.sqrt (pi i) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpi0 i)]
    rw [hsq]
    field_simp
  have hw : ∀ i, s (whitenedVector pi v i) = (Real.sqrt (pi i) : ℂ) • v i := by
    intro i
    obtain ⟨u, hu⟩ := hpre i
    unfold whitenedVector
    rw [hva]
    exact inv_root_spec _ _ u hu hinj
  refine ⟨fun i => by rw [hva]; exact hw i, ?_⟩
  set w := whitenedVector pi v with hwdef
  -- Parseval identity on the range of s
  have hK : ∀ y, HasSum (fun i => ‖inner ℂ (w i) (s y)‖ ^ 2) (‖s y‖ ^ 2) := by
    intro y
    have h := hform y
    rw [← hss, ContinuousLinearMap.mul_apply, sa_swap hsa y (s y),
      show (inner ℂ (s y) (s y)).re = ‖s y‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) (s y)] at h
    have hf : (fun i => ‖inner ℂ (w i) (s y)‖ ^ 2) =
        fun j => pi j * (inner ℂ y (boundedOperator (rho j).coefficients y)).re := by
      funext i
      have e1 : inner ℂ (w i) (s y) = (Real.sqrt (pi i) : ℂ) * inner ℂ (v i) y := by
        rw [sa_swap hsa, hw i, inner_smul_left, Complex.conj_ofReal]
      have e2 : (inner ℂ y (boundedOperator (rho i).coefficients y)).re =
          ‖inner ℂ (v i) y‖ ^ 2 := by
        rw [(hv i).2, bO_rankOne, ← inner_conj_symm, inner_rk_self, Complex.conj_ofReal,
          Complex.ofReal_re]
      rw [e1, e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
        Real.sq_sqrt (hpi0 i)]
    rw [hf]
    exact h
  have hb : ∀ x, ∀ F : Finset L, ∑ i ∈ F, ‖inner ℂ (w i) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x F
    refine hdense.induction_on (p := fun x => ∑ i ∈ F, ‖inner ℂ (w i) x‖ ^ 2 ≤ ‖x‖ ^ 2) x
      (isClosed_le (by fun_prop) (by fun_prop)) (fun y => ?_)
    exact sum_le_hasSum F (fun i _ => by positivity) (hK y)
  have hiso : ∀ x, ‖anaOp w hb x‖ = ‖x‖ := by
    intro x
    refine hdense.induction_on (p := fun x => ‖anaOp w hb x‖ = ‖x‖) x
      (isClosed_eq (continuous_norm.comp (anaOp w hb).continuous) continuous_norm) (fun y => ?_)
    have h1 := hasSum_normSq (anaOp w hb (s y))
    have h2 : ‖anaOp w hb (s y)‖ ^ 2 = ‖s y‖ ^ 2 := h1.unique (hK y)
    have := norm_nonneg (anaOp w hb (s y))
    have := norm_nonneg (s y)
    exact le_antisymm (by nlinarith) (by nlinarith)
  exact parseval_of_iso w hb hiso

end P45N2

end

end N2A

section N2B

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace P45N2

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator IsParsevalFrame)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)
open P45Petz P45N0 P45N1 P45N1A

/-- Cancellation through an injective, dense-range sandwich. -/
lemma sandwich_cancel {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s T T' : E →L[ℂ] E} (hinj : Function.Injective s) (hdense : DenseRange s)
    (h : s.comp (T.comp s) = s.comp (T'.comp s)) : T = T' := by
  have h1 : ∀ x, T (s x) = T' (s x) := fun x =>
    hinj (by simpa using congrArg (fun A : E →L[ℂ] E => A x) h)
  exact ContinuousLinearMap.ext fun y =>
    hdense.induction_on (p := fun y => T y = T' y) y (isClosed_eq T.continuous T'.continuous) h1

theorem n2b {I L : Type} [Countable I] (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) (v : L → Hilbert I)
    (hv : ∀ i, ‖v i‖ = 1 ∧ (rho i).coefficients = rankOne (v i))
    (pi : L → ℝ) (sigma : State I) (hpi : PositiveLaw pi)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b)
    (i : L) (X : Hilbert I →L[ℂ] Hilbert I)
    (h1 : (positiveSquareRoot (boundedOperator sigma.coefficients)).comp
        (X.comp (positiveSquareRoot (boundedOperator sigma.coefficients))) =
      (pi i : ℂ) • boundedOperator (rho i).coefficients) :
    X = rk (whitenedVector pi v i) (whitenedVector pi v i) := by
  have hpi0 : ∀ j, 0 ≤ pi j := fun j => (hpi.1 j).le
  have hva : vectorAverage pi v = sigma.coefficients := by
    rw [hbar]
    funext a b
    simp only [vectorAverage, (hv _).2]
  obtain ⟨hwa, _⟩ := n2a rho hC v hv pi sigma hpi hbar
  obtain ⟨hinj, hdense⟩ := sqrt_inj_dense rho hC hpi sigma hbar
  obtain ⟨hsa, _, _⟩ := sqrt_state sigma
  have hw : positiveSquareRoot (boundedOperator sigma.coefficients) (whitenedVector pi v i) =
      (Real.sqrt (pi i) : ℂ) • v i := by
    have := hwa i
    rw [hva] at this
    exact this
  set s := positiveSquareRoot (boundedOperator sigma.coefficients) with hsdef
  set w := whitenedVector pi v i with hwdef
  have h2 : s.comp ((rk w w).comp s) = (pi i : ℂ) • boundedOperator (rho i).coefficients := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, rk_apply, map_smul]
    rw [sa_swap hsa w x, hw, (hv i).2, bO_rankOne, rk_apply, inner_smul_left, Complex.conj_ofReal,
      smul_smul, smul_smul]
    congr 1
    have hsq : (pi i : ℂ) = (Real.sqrt (pi i) : ℂ) * (Real.sqrt (pi i) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpi0 i)]
    rw [hsq]
    ring
  exact sandwich_cancel hinj hdense (h1.trans h2.symm)






end P45N2

end

end N2B

section N2PS

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace P45N2P

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator IsParsevalFrame)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)


end P45N2P

end

end N2PS

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
theorem solution {I L : Type} [Countable I] (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) (v : L → Hilbert I)
    (hv : ∀ i, ‖v i‖ = 1 ∧ (rho i).coefficients = rankOne (v i))
    (pi : L → ℝ) (sigma : State I) (hpi : PositiveLaw pi)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    (∀ i, positiveSquareRoot (boundedOperator (vectorAverage pi v)) (whitenedVector pi v i) =
      (Real.sqrt (pi i) : ℂ) • v i) ∧ IsParsevalFrame (whitenedVector pi v) ∧
    ∀ (i : L) (X : Hilbert I →L[ℂ] Hilbert I),
      (positiveSquareRoot (boundedOperator sigma.coefficients)).comp
          (X.comp (positiveSquareRoot (boundedOperator sigma.coefficients))) =
        (pi i : ℂ) • boundedOperator (rho i).coefficients →
      X = (innerSL ℂ (whitenedVector pi v i)).smulRight (whitenedVector pi v i) := by
  obtain ⟨h1, h2⟩ := P45N2.n2a rho hC v hv pi sigma hpi hbar
  exact ⟨h1, h2, fun i X hX => P45N2.n2b rho hC v hv pi sigma hpi hbar i X hX⟩

end

end ChildRoot
