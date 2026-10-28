-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.complement_kraus_rankOne_of_output_resolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:10:01.203073+00:00
-- url     : https://prove2.me/submissions/e6c645bc-3cfa-4944-aaac-47b5f09a7ea9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
set_option Elab.async false

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology

attribute [local instance] Classical.propDecidable

namespace P45D
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
noncomputable local instance (priority := 1100) scC_nacg_1 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : NormedAddCommGroup (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scH_am_1 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_1 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_1 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_1 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
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

lemma bessel_fin (A : K → H →L[ℂ] F) (hA : ∀ u, HasSum (fun k => ‖A k u‖ ^ 2) (‖u‖ ^ 2))
    (G : Finset K) (w : K → F) :
    ‖∑ k ∈ G, ContinuousLinearMap.adjoint (A k) (w k)‖ ^ 2 ≤ ∑ k ∈ G, ‖w k‖ ^ 2 := by
  set z := ∑ k ∈ G, ContinuousLinearMap.adjoint (A k) (w k) with hz_def
  have hP : ∑ k ∈ G, ‖A k z‖ ^ 2 ≤ ‖z‖ ^ 2 :=
    sum_le_hasSum G (fun _ _ => sq_nonneg _) (hA z)
  have e : inner ℂ z z = ∑ k ∈ G, inner ℂ (A k z) (w k) := by
    calc inner ℂ z z = inner ℂ z (∑ k ∈ G, ContinuousLinearMap.adjoint (A k) (w k)) := by
          rw [← hz_def]
      _ = _ := by rw [inner_sum]; simp only [ContinuousLinearMap.adjoint_inner_right]
  have hz : ‖z‖ ^ 2 ≤ ∑ k ∈ G, ‖A k z‖ * ‖w k‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) z, e, map_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hT2 := Finset.sum_mul_sq_le_sq_mul_sq G (fun k => ‖A k z‖) (fun k => ‖w k‖)
  have hQ : 0 ≤ ∑ k ∈ G, ‖w k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT : 0 ≤ ∑ k ∈ G, ‖A k z‖ * ‖w k‖ := Finset.sum_nonneg (fun _ _ => by positivity)
  have h1 := mul_self_le_mul_self (sq_nonneg ‖z‖) hz
  have h2 := mul_le_mul_of_nonneg_right hP hQ
  by_contra hcon
  push Not at hcon
  have hpos : 0 < ‖z‖ ^ 2 := lt_of_le_of_lt hQ hcon
  nlinarith [mul_lt_mul_of_pos_left hcon hpos]

lemma kraus_strong (A : K → H →L[ℂ] F) (hA : ∀ u, HasSum (fun k => ‖A k u‖ ^ 2) (‖u‖ ^ 2))
    (u : H) : HasSum (fun k => ((ContinuousLinearMap.adjoint (A k)).comp (A k)) u) u := by
  have hfin : ∀ G : Finset K,
      ‖∑ k ∈ G, ((ContinuousLinearMap.adjoint (A k)).comp (A k)) u‖ ^ 2 ≤ ∑ k ∈ G, ‖A k u‖ ^ 2 :=
    fun G => bessel_fin A hA G (fun k => A k u)
  have hs : Summable (fun k => ((ContinuousLinearMap.adjoint (A k)).comp (A k)) u) := by
    refine summable_iff_vanishing_norm.mpr (fun ε hε => ?_)
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp (hA u).summable (ε ^ 2) (by positivity)
    refine ⟨s, fun t ht => ?_⟩
    have h1 := hfin t
    have h2 := hs t ht
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at h2
    nlinarith [norm_nonneg (∑ k ∈ t, ((ContinuousLinearMap.adjoint (A k)).comp (A k)) u)]
  obtain ⟨L, hL⟩ := hs
  have hLn : ‖L‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have ht := (Filter.Tendsto.norm hL).pow 2
    exact le_of_tendsto' ht
      (fun G => (hfin G).trans (sum_le_hasSum G (fun _ _ => sq_nonneg _) (hA u)))
  have hin : inner ℂ u L = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    have h1 := hL.mapL (innerSL ℂ u)
    have h2 : HasSum (fun k => ((‖A k u‖ ^ 2 : ℝ) : ℂ)) ((‖u‖ ^ 2 : ℝ) : ℂ) :=
      Complex.hasSum_ofReal.mpr (hA u)
    have e : ∀ k, (innerSL ℂ u) (((ContinuousLinearMap.adjoint (A k)).comp (A k)) u) =
        ((‖A k u‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [innerSL_apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq_to_K]
      first | rfl | norm_cast | simp
    simp only [e] at h1
    exact h1.unique h2
  have hre : RCLike.re (inner ℂ L u) = ‖u‖ ^ 2 := by
    rw [← inner_conj_symm, hin, Complex.conj_ofReal]
    exact Complex.ofReal_re _
  have hsq : ‖L - u‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hre]
    nlinarith [hLn]
  have h0 : ‖L - u‖ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  have h00 : L = u := sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))
  rw [h00] at hL
  exact hL

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

lemma outerOp_form {J E : Type} (y : Hilbert (J × E)) (x : Hilbert J) :
    HasSum (fun e => ((‖inner ℂ (sliceV e y) x‖ ^ 2 : ℝ) : ℂ)) (inner ℂ x (outerOp y y x)) := by
  have h := (summable_outer_terms y y x).hasSum.mapL (innerSL ℂ x)
  rw [← outerOp_apply] at h
  have e : ∀ e', (innerSL ℂ x) (inner ℂ (sliceV e' y) x • sliceV e' y) =
      ((‖inner ℂ (sliceV e' y) x‖ ^ 2 : ℝ) : ℂ) := by
    intro e'
    rw [innerSL_apply_apply, inner_smul_right, ← inner_conj_symm x (sliceV e' y), RCLike.mul_conj]
    first | rfl | norm_cast | simp
  simp only [e] at h
  exact h

lemma slice_mem_closure_range {J E : Type} (y : Hilbert (J × E)) (e : E) :
    sliceV e y ∈ (LinearMap.range (outerOp y y).toLinearMap).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro x hx
  have h0 : inner ℂ x (outerOp y y x) = 0 := by
    rw [Submodule.mem_orthogonal] at hx
    have := hx (outerOp y y x) ⟨x, rfl⟩
    rw [← inner_conj_symm, this, map_zero]
  have h := outerOp_form y x
  rw [h0, ← Complex.ofReal_zero] at h
  have hr := Complex.hasSum_ofReal.mp h
  have h1 := (hasSum_zero_iff_of_nonneg (fun _ => sq_nonneg _)).mp hr
  have hz : ‖inner ℂ (sliceV e y) x‖ ^ 2 = 0 := congrFun h1 e
  have h2 : inner ℂ (sliceV e y) x = 0 := by
    rwa [sq_eq_zero_iff, norm_eq_zero] at hz
  rw [← inner_conj_symm, h2, map_zero]

lemma slice_in_output {I J E : Type} {Phi : Channel I J} {Psi : Channel I E}
    (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (u : Hilbert I) (e : E) :
    sliceV e (V u) ∈ outputSpace Phi.val := by
  by_cases hu : u = 0
  · subst hu
    have h0 : sliceV e (V 0) = 0 := by ext t; simp
    rw [h0]; exact Submodule.zero_mem _
  · have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    obtain ⟨t, w, hw, hu'⟩ : ∃ (t : ℂ) (w : Hilbert I), ‖w‖ = 1 ∧ u = t • w := by
      refine ⟨((‖u‖ : ℝ) : ℂ), (((‖u‖ : ℝ) : ℂ))⁻¹ • u, ?_, ?_⟩
      · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
        exact inv_mul_cancel₀ hn
      · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]
    have hsl : sliceV e (V u) = t • sliceV e (V w) := by rw [hu', map_smul, sliceV_smul]
    rw [hsl]
    refine Submodule.smul_mem _ _ ?_
    have hmem := slice_mem_closure_range (V w) e
    refine Submodule.topologicalClosure_mono ?_ hmem
    rintro v ⟨x, rfl⟩
    refine Submodule.subset_span ⟨pureOf w hw, x, ?_⟩
    change boundedOperator (Phi.val (rankOne w)) x = outerOp (V w) (V w) x
    rw [phi_rankOne_all V hV w, bO_traceSecond_outer]

lemma outputProjection_fix {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (v : Hilbert J)
    (hv : v ∈ outputSpace Phi) : outputProjection Phi v = v := by
  letI : CompleteSpace (outputSpace Phi) :=
    (show IsClosed (outputSpace Phi : Set (Hilbert J)) from
      Submodule.isClosed_topologicalClosure _).completeSpace_coe
  unfold outputProjection
  exact Submodule.starProjection_eq_self_iff.mpr hv

/-- First clause of `IsKrausRepresentation` for `A_k = (<ψ_k| ⊗ 1) V`. -/
lemma kraus_first {I J E K : Type} {Phi : Channel I J} {Psi : Channel I E}
    (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (psi : K → Hilbert J)
    (hpsi : ∀ x, HasSum (fun k => ‖inner ℂ (psi k) x‖ ^ 2)
      (inner ℂ x (outputProjection Phi.val x)).re) (x : Hilbert I) :
    HasSum (fun k => ((ContinuousLinearMap.adjoint ((braL (E := E) (psi k)).comp
      V.toContinuousLinearMap)).comp ((braL (psi k)).comp V.toContinuousLinearMap)) x) x :=
  kraus_strong (fun k => (braL (E := E) (psi k)).comp V.toContinuousLinearMap)
    (kraus_norm V (outputProjection Phi.val) psi hpsi
      (fun u e => outputProjection_fix _ _ (slice_in_output V hV u e))) x

end P45D

/-! ## ALem2 (Lemma 2 of Shirokov, restricted form) -- session 6 -/

namespace P45L
noncomputable local instance (priority := 1100) scH_nacg_2 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_2 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_2 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_2 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_2 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_2 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_2 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scC_acm_2 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_mod_2 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Module ℂ (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scH_am_2 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_2 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_2 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_acm_2 (X Y : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_mod_2 (X Y : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
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

open scoped BigOperators ENNReal ComplexConjugate Topology
open Filter

attribute [local instance] Classical.propDecidable

namespace P45K
noncomputable local instance (priority := 1100) scH_nacg_3 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_3 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_3 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_3 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_3 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_3 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ns_3 (X : Type) : NormedSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_3 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scC_acm_3 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_top_3 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : TopologicalSpace (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scH_am_3 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_3 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_3 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_3 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_acm_3 (X Y : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_top_3 (X Y : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_snacg_3 (X Y : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
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
noncomputable local instance (priority := 1100) scA_bcadd_3 (X : Type) : ContinuousAdd (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_btag_3 (X : Type) : IsTopologicalAddGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bccs_3 (X : Type) : ContinuousConstSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcs_3 (X : Type) : ContinuousSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bt2_3 (X : Type) : T2Space (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_badd_3 (X : Type) : Add (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bsmul_3 (X : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcladd_3 (X Y : Type) : Add (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsub_3 (X Y : Type) : Sub (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsmul_3 (X Y : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclmul_3 (X : Type) : Mul (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bclfun_3 (X Y : Type) : FunLike (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) (QAlgorithms.RealRegisters.Hilbert X) (QAlgorithms.RealRegisters.Hilbert Y) := inferInstance

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

def absV {I : Type} (u : Hilbert I) : Hilbert I :=
  ⟨fun i => ((‖u i‖ : ℝ) : ℂ), by
    have h : Memℓp (fun i => ‖u i‖) 2 := memℓp_norm_iff.mpr u.2
    apply memℓp_norm_iff.mp
    simpa using h⟩

lemma absV_apply {I : Type} (u : Hilbert I) (i : I) : absV u i = ((‖u i‖ : ℝ) : ℂ) := rfl

lemma norm_absV {I : Type} (u : Hilbert I) : ‖absV u‖ = ‖u‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 2
  funext i
  rw [absV_apply]
  simp

lemma cs_coord {I : Type} (u v : Hilbert I) :
    Summable (fun i => ‖u i‖ * ‖v i‖) ∧ ∑' i, ‖u i‖ * ‖v i‖ ≤ ‖u‖ * ‖v‖ := by
  have hs := lp.summable_inner (𝕜 := ℂ) (absV u) (absV v)
  have hfun : (fun i => inner ℂ (absV u i) (absV v i)) = fun i => ((‖u i‖ * ‖v i‖ : ℝ) : ℂ) := by
    funext i
    rw [absV_apply, absV_apply]
    simp [mul_comm]
  rw [hfun] at hs
  have hsR : Summable (fun i => ‖u i‖ * ‖v i‖) := Complex.summable_ofReal.mp hs
  refine ⟨hsR, ?_⟩
  have hin : inner ℂ (absV u) (absV v) = ((∑' i, ‖u i‖ * ‖v i‖ : ℝ) : ℂ) := by
    rw [lp.inner_eq_tsum, hfun, Complex.ofReal_tsum]
  have := norm_inner_le_norm (𝕜 := ℂ) (absV u) (absV v)
  rw [hin, norm_absV, norm_absV, Complex.norm_real, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

lemma V_coord {T U : Type} (V : Hilbert T →L[ℂ] Hilbert U) (u : Hilbert T) (p : U) :
    HasSum (fun i => u i * (V (lp.single 2 i (1 : ℂ))) p) ((V u) p) := by
  have h := hasSum_coord ((hasSum_basis u).map V V.continuous) p
  convert h using 1
  funext i
  simp [Function.comp, map_smul]

lemma norm_coord_le {T : Type} (x : Hilbert T) (t : T) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by norm_num) x t

/-! ## K3.1 balanced nuclear expansions -/

lemma balance {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    ∃ e' : NuclearExpansion X, ∀ n, ‖e'.left n‖ ^ 2 = ‖e.left n‖ * ‖e.right n‖ ∧
      ‖e'.right n‖ ^ 2 = ‖e.left n‖ * ‖e.right n‖ := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun n => ‖e.left n‖ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun n => ‖e.right n‖ := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℝ, α = fun n => Real.sqrt (b n / a n) := ⟨_, rfl⟩
  have ha0 : ∀ n, 0 ≤ a n := fun n => by rw [ha]; exact norm_nonneg _
  have hb0 : ∀ n, 0 ≤ b n := fun n => by rw [hb]; exact norm_nonneg _
  have hαn : ∀ n, 0 ≤ α n := fun n => by rw [hα]; exact Real.sqrt_nonneg _
  have hαsq : ∀ n, α n ^ 2 = b n / a n := fun n => by
    rw [hα]; exact Real.sq_sqrt (div_nonneg (hb0 n) (ha0 n))
  have hα0 : ∀ n, α n = 0 → e.left n = 0 ∨ e.right n = 0 := by
    intro n h
    have h3 : b n / a n = 0 := by rw [← hαsq, h]; ring
    rcases div_eq_zero_iff.mp h3 with h4 | h4
    · right; rw [hb] at h4; exact norm_eq_zero.mp h4
    · left; rw [ha] at h4; exact norm_eq_zero.mp h4
  have hL : ∀ n, ‖((α n : ℂ)) • e.left n‖ ^ 2 = ‖e.left n‖ * ‖e.right n‖ := by
    intro n
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hαn n), mul_pow, hαsq]
    have h1 : ‖e.left n‖ = a n := by rw [ha]
    have h2 : ‖e.right n‖ = b n := by rw [hb]
    rw [h1, h2]
    rcases eq_or_ne (a n) 0 with h | h
    · simp [h]
    · field_simp
  have hR : ∀ n, ‖((α n : ℂ))⁻¹ • e.right n‖ ^ 2 = ‖e.left n‖ * ‖e.right n‖ := by
    intro n
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hαn n), mul_pow,
      inv_pow, hαsq]
    have h1 : ‖e.left n‖ = a n := by rw [ha]
    have h2 : ‖e.right n‖ = b n := by rw [hb]
    rw [h1, h2]
    rcases eq_or_ne (a n) 0 with h | h
    · simp [h]
    rcases eq_or_ne (b n) 0 with h' | h'
    · simp [h']
    field_simp
  refine ⟨{ left := fun n => ((α n : ℂ)) • e.left n
            right := fun n => ((α n : ℂ))⁻¹ • e.right n
            summable := ?_
            coefficients := ?_ }, fun n => ⟨hL n, hR n⟩⟩
  · refine e.summable.congr (fun n => ?_)
    have hp : (‖((α n : ℂ)) • e.left n‖ * ‖((α n : ℂ))⁻¹ • e.right n‖) ^ 2 =
        (‖e.left n‖ * ‖e.right n‖) ^ 2 := by
      rw [mul_pow, hL, hR]; ring
    exact ((pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp hp).symm
  · intro i j
    rw [e.coefficients i j]
    refine tsum_congr (fun n => ?_)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases h : α n = 0
    · rcases hα0 n h with h' | h' <;> simp [h, h']
    · have h'' : ((α n : ℂ)) ≠ 0 := by exact_mod_cast h
      rw [star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal]
      field_simp

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

lemma vec_polar {J : Type} (x y : Hilbert J) :
    ∑ c ∈ Finset.range 4, (Complex.I ^ c / 4) * (((‖x + Complex.I ^ c • y‖ ^ 2 : ℝ)) : ℂ) =
      inner ℂ y x := by
  have hn : ∀ z : Hilbert J, (((‖z‖ ^ 2 : ℝ)) : ℂ) = inner ℂ z z := fun z => by
    rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]; rfl
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  simp only [hn, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Complex.I_sq, h3,
    map_one, map_neg, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four, h3]
  ring

lemma frame_polar {J K : Type} (P : Hilbert J →L[ℂ] Hilbert J) (psi : K → Hilbert J)
    (hpsi : ∀ x, HasSum (fun k => ‖inner ℂ (psi k) x‖ ^ 2) (inner ℂ x (P x)).re)
    (x y : Hilbert J) (hx : P x = x) (hy : P y = y) :
    HasSum (fun k => inner ℂ (psi k) x * star (inner ℂ (psi k) y)) (inner ℂ y x) := by
  have hc : ∀ c ∈ Finset.range 4, HasSum (fun k => (Complex.I ^ c / 4) *
      (((‖inner ℂ (psi k) (x + Complex.I ^ c • y)‖ ^ 2 : ℝ)) : ℂ))
      ((Complex.I ^ c / 4) * ((‖x + Complex.I ^ c • y‖ ^ 2 : ℝ) : ℂ)) := by
    intro c _
    have h := hpsi (x + Complex.I ^ c • y)
    rw [map_add, map_smul, hx, hy] at h
    rw [show (inner ℂ (x + Complex.I ^ c • y) (x + Complex.I ^ c • y)).re =
      ‖x + Complex.I ^ c • y‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) _] at h
    exact (Complex.hasSum_ofReal.mpr h).mul_left _
  have hs := hasSum_sum hc
  rw [vec_polar] at hs
  convert hs using 1
  funext k
  rw [← polar4 (inner ℂ (psi k) x) (inner ℂ (psi k) y) (inner ℂ (psi k) x) (inner ℂ (psi k) y)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [inner_add_right, inner_smul_right, Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]

/-! ## K3.3 double-series swap -/


lemma summable_uncurry_of_swap {α β : Type} (g : α → β → ℝ) (hg0 : ∀ a b, 0 ≤ g a b)
    (hg1 : ∀ b, Summable (fun a => g a b)) (hg2 : Summable (fun b => ∑' a, g a b)) :
    Summable (Function.uncurry g) := by
  have hu : Summable (Function.uncurry (fun b a => g a b)) :=
    (summable_prod_of_nonneg (fun p => hg0 p.2 p.1)).2 ⟨hg1, hg2⟩
  have := (Equiv.prodComm α β).summable_iff.mpr hu
  exact this

lemma tsum_swap_of {α β : Type} (f : α → β → ℂ) (g : α → β → ℝ)
    (hfg : ∀ a b, ‖f a b‖ ≤ g a b) (hu : Summable (Function.uncurry g)) :
    (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b := by
  have hf : Summable (Function.uncurry f) :=
    Summable.of_norm_bounded hu (fun p => hfg p.1 p.2)
  exact hf.tsum_comm.symm

/-! ## K3.4 conjugating a nuclear expansion: `boundedConjugation` and `traceFirst` -/

lemma V_single_eq {T U : Type} (V : Hilbert T →L[ℂ] Hilbert U) (p : U) (i : T) :
    (V (lp.single 2 i (1:ℂ))) p =
      star ((ContinuousLinearMap.adjoint V (lp.single 2 p (1:ℂ))) i) := by
  have h1 := inner_single_right' (V (lp.single 2 i (1:ℂ))) p
  rw [← ContinuousLinearMap.adjoint_inner_right, lp.inner_single_left] at h1
  rw [RCLike.inner_apply, map_one, mul_one] at h1
  rw [h1, star_star]

lemma norm_V_single {T U : Type} (V : Hilbert T →L[ℂ] Hilbert U) (p : U) (i : T) :
    ‖(V (lp.single 2 i (1:ℂ))) p‖ = ‖(ContinuousLinearMap.adjoint V (lp.single 2 p (1:ℂ))) i‖ := by
  rw [V_single_eq, norm_star]

lemma norm_V_coord_le {T U : Type} (V : Hilbert T →L[ℂ] Hilbert U) (u : Hilbert T) (p : U) :
    ‖(V u) p‖ ≤ ‖V‖ * ‖u‖ := (norm_coord_le _ p).trans (V.le_opNorm u)

lemma bconj_nuc_eq {T U : Type} (V : Hilbert T →L[ℂ] Hilbert U) {Z : Matrix T T ℂ}
    (e : NuclearExpansion Z) (p q : U) :
    boundedConjugation V Z p q =
      ∑' n, (V (e.left n)) p * star ((V (e.right n)) q) := by
  set β := ContinuousLinearMap.adjoint V (lp.single 2 p (1:ℂ))
  set γ := ContinuousLinearMap.adjoint V (lp.single 2 q (1:ℂ))
  have stepA : ∀ i, (∑' j, (V (lp.single 2 i (1:ℂ))) p * Z i j *
      star ((V (lp.single 2 j (1:ℂ))) q)) =
      (V (lp.single 2 i (1:ℂ))) p * ∑' n, e.left n i * star ((V (e.right n)) q) := by
    intro i
    set ai := (V (lp.single 2 i (1:ℂ))) p
    calc (∑' j, ai * Z i j * star ((V (lp.single 2 j (1:ℂ))) q))
        = ∑' j, ∑' n, ai * (e.left n i * star (e.right n j)) *
            star ((V (lp.single 2 j (1:ℂ))) q) := by
          refine tsum_congr (fun j => ?_)
          rw [e.coefficients i j, ← tsum_mul_left, ← tsum_mul_right]
      _ = ∑' n, ∑' j, ai * (e.left n i * star (e.right n j)) *
            star ((V (lp.single 2 j (1:ℂ))) q) := by
          refine tsum_swap_of _ (fun j n => ‖ai‖ * ‖e.left n‖ * (‖e.right n j‖ * ‖γ j‖))
            (fun j n => ?_) ?_
          · rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star, norm_V_single V q j]
            have := norm_coord_le (e.left n) i
            have h0 : 0 ≤ ‖e.right n j‖ * ‖γ j‖ := by positivity
            calc ‖ai‖ * (‖e.left n i‖ * ‖e.right n j‖) * ‖γ j‖
                = ‖ai‖ * ‖e.left n i‖ * (‖e.right n j‖ * ‖γ j‖) := by ring
              _ ≤ ‖ai‖ * ‖e.left n‖ * (‖e.right n j‖ * ‖γ j‖) := by gcongr
          · refine summable_uncurry_of_swap _ (fun _ _ => by positivity) (fun n => ?_) ?_
            · exact (cs_coord (e.right n) γ).1.mul_left _
            · refine Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => by positivity))
                (fun n => ?_) (e.summable.mul_left (‖ai‖ * ‖γ‖))
              rw [tsum_mul_left]
              calc ‖ai‖ * ‖e.left n‖ * ∑' j, ‖e.right n j‖ * ‖γ j‖
                  ≤ ‖ai‖ * ‖e.left n‖ * (‖e.right n‖ * ‖γ‖) := by
                    gcongr; exact (cs_coord (e.right n) γ).2
                _ = ‖ai‖ * ‖γ‖ * (‖e.left n‖ * ‖e.right n‖) := by ring
      _ = ∑' n, ai * (e.left n i * star ((V (e.right n)) q)) := by
          refine tsum_congr (fun n => ?_)
          have h := ((V_coord V (e.right n) q).star).mul_left (ai * e.left n i)
          rw [← mul_assoc, ← h.tsum_eq]
          refine tsum_congr (fun j => ?_)
          rw [star_mul']
          ring
      _ = ai * ∑' n, e.left n i * star ((V (e.right n)) q) := tsum_mul_left
  unfold boundedConjugation
  simp_rw [stepA]
  set s : ℕ → ℂ := fun n => star ((V (e.right n)) q)
  calc (∑' i, (V (lp.single 2 i (1:ℂ))) p * ∑' n, e.left n i * s n)
      = ∑' i, ∑' n, (V (lp.single 2 i (1:ℂ))) p * (e.left n i * s n) := by
        refine tsum_congr (fun i => ?_); rw [tsum_mul_left]
    _ = ∑' n, ∑' i, (V (lp.single 2 i (1:ℂ))) p * (e.left n i * s n) := by
        refine tsum_swap_of _ (fun i n => ‖β i‖ * ‖e.left n i‖ * (‖V‖ * ‖e.right n‖))
          (fun i n => ?_) ?_
        · rw [norm_mul, norm_mul, norm_V_single V p i]
          have : ‖s n‖ ≤ ‖V‖ * ‖e.right n‖ := by
            simp only [s, norm_star]; exact norm_V_coord_le V _ q
          calc ‖β i‖ * (‖e.left n i‖ * ‖s n‖) = ‖β i‖ * ‖e.left n i‖ * ‖s n‖ := by ring
            _ ≤ _ := by gcongr
        · refine summable_uncurry_of_swap _ (fun _ _ => by positivity) (fun n => ?_) ?_
          · exact ((cs_coord β (e.left n)).1).mul_right _
          · refine Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => by positivity))
              (fun n => ?_) (e.summable.mul_left (‖β‖ * ‖V‖))
            rw [tsum_mul_right]
            calc (∑' i, ‖β i‖ * ‖e.left n i‖) * (‖V‖ * ‖e.right n‖)
                ≤ (‖β‖ * ‖e.left n‖) * (‖V‖ * ‖e.right n‖) := by
                  gcongr; exact (cs_coord β (e.left n)).2
              _ = ‖β‖ * ‖V‖ * (‖e.left n‖ * ‖e.right n‖) := by ring
    _ = ∑' n, (V (e.left n)) p * s n := by
        refine tsum_congr (fun n => ?_)
        rw [← (V_coord V (e.left n) p).tsum_eq, ← tsum_mul_right]
        refine tsum_congr (fun i => ?_)
        ring


lemma traceFirst_bconj_nuc {T J E : Type} (V : Hilbert T →L[ℂ] Hilbert (J × E))
    {Z : Matrix T T ℂ} (e : NuclearExpansion Z) (a b : E) :
    HasSum (fun n => ∑' j, (V (e.left n)) (j, a) * star ((V (e.right n)) (j, b)))
      (traceFirst (boundedConjugation V Z) a b) := by
  have hcs : ∀ n, Summable (fun j : J => ‖(V (e.left n)) (j, a)‖ * ‖(V (e.right n)) (j, b)‖) ∧
      ∑' j : J, ‖(V (e.left n)) (j, a)‖ * ‖(V (e.right n)) (j, b)‖ ≤
        ‖V‖ * ‖V‖ * (‖e.left n‖ * ‖e.right n‖) := by
    intro n
    have h := cs_coord (sliceV a (V (e.left n))) (sliceV b (V (e.right n)))
    refine ⟨h.1, h.2.trans ?_⟩
    calc ‖sliceV a (V (e.left n))‖ * ‖sliceV b (V (e.right n))‖
        ≤ (‖V‖ * ‖e.left n‖) * (‖V‖ * ‖e.right n‖) :=
          mul_le_mul ((norm_sliceV_le' _ _).trans (V.le_opNorm _))
            ((norm_sliceV_le' _ _).trans (V.le_opNorm _)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hsum : Summable (fun n => ∑' j, (V (e.left n)) (j, a) * star ((V (e.right n)) (j, b))) := by
    refine Summable.of_norm_bounded (e.summable.mul_left (‖V‖ * ‖V‖)) (fun n => ?_)
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · refine (hcs n).1.congr (fun j => ?_); rw [norm_mul, norm_star]
    · refine le_trans (le_of_eq (tsum_congr (fun j => ?_))) (hcs n).2
      rw [norm_mul, norm_star]
  convert hsum.hasSum using 1
  unfold traceFirst
  simp_rw [bconj_nuc_eq V e]
  refine tsum_swap_of _ (fun j n => ‖(V (e.left n)) (j, a)‖ * ‖(V (e.right n)) (j, b)‖)
    (fun j n => by rw [norm_mul, norm_star]) ?_
  refine summable_uncurry_of_swap _ (fun _ _ => by positivity) (fun n => (hcs n).1) ?_
  exact Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => by positivity))
    (fun n => (hcs n).2) (e.summable.mul_left _)

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

lemma chan_zero {I J : Type} (Phi : Channel I J) : Phi.val 0 = 0 := by
  have h := Phi.property.2.2.1 0 0 tc_zero
  rw [zero_smul, zero_smul] at h
  exact h

lemma tc_sum {T : Type} (m : ℕ) (c : ℕ → ℂ) (Y : ℕ → Matrix T T ℂ)
    (hY : ∀ k, IsTraceClass (Y k)) : IsTraceClass (∑ k ∈ Finset.range m, c k • Y k) := by
  induction m with
  | zero => simpa using tc_zero
  | succ m ih => rw [Finset.sum_range_succ]; exact tc_add ih (tc_smul _ (hY m))

lemma chan_sum {I J : Type} (Phi : Channel I J) (m : ℕ) (c : ℕ → ℂ) (Y : ℕ → Matrix I I ℂ)
    (hY : ∀ k, IsTraceClass (Y k)) :
    Phi.val (∑ k ∈ Finset.range m, c k • Y k) = ∑ k ∈ Finset.range m, c k • Phi.val (Y k) := by
  induction m with
  | zero => simpa using chan_zero Phi
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Phi.property.2.1 _ _ (tc_sum m c Y hY) (tc_smul _ (hY m)), ih,
      Phi.property.2.2.1 _ _ (hY m)]

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

lemma mat_coeff_summable {T : Type} (w : ℕ → Hilbert T) (hw : Summable (fun n => ‖w n‖ ^ 2))
    (i j : T) : Summable (fun n => w n i * star (w n j)) := by
  refine Summable.of_norm_bounded hw (fun n => ?_)
  rw [norm_mul, norm_star, sq]
  exact mul_le_mul (norm_coord_le _ _) (norm_coord_le _ _) (norm_nonneg _) (norm_nonneg _)

def matExp {T : Type} (c : ℂ) (w : ℕ → Hilbert T) (hw : Summable (fun n => ‖w n‖ ^ 2)) :
    NuclearExpansion (c • Mat w) where
  left := fun n => c • w n
  right := w
  summable := (hw.mul_left ‖c‖).congr (fun n => by rw [norm_smul, sq]; ring)
  coefficients := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, Mat]
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    simp [mul_assoc]

lemma tc_mat {T : Type} (w : ℕ → Hilbert T) (hw : Summable (fun n => ‖w n‖ ^ 2)) :
    IsTraceClass (Mat w) := by
  have h : IsTraceClass ((1:ℂ) • Mat w) := ⟨matExp 1 w hw⟩
  rwa [one_smul] at h

lemma isDensity_mat {T : Type} (w : ℕ → Hilbert T) (hw : Summable (fun n => ‖w n‖ ^ 2))
    (hs : (∑' n, ‖w n‖ ^ 2) ≠ 0) :
    IsDensity ((((∑' n, ‖w n‖ ^ 2)⁻¹ : ℝ) : ℂ) • Mat w) := by
  set s := ∑' n, ‖w n‖ ^ 2 with hsdef
  set c : ℂ := ((s⁻¹ : ℝ) : ℂ) with hc
  have hs0 : 0 ≤ s := tsum_nonneg (fun _ => sq_nonneg _)
  refine ⟨⟨matExp c w hw⟩, fun S z => ?_, ?_⟩
  · have hterm : ∀ i j, HasSum (fun n => star (z i) * (c * (w n i * star (w n j))) * z j)
        (star (z i) * (c • Mat w) i j * z j) := by
      intro i j
      have h := (((mat_coeff_summable w hw i j).hasSum.mul_left c).mul_left (star (z i))).mul_right
        (z j)
      simpa only [Matrix.smul_apply, smul_eq_mul, Mat] using h
    have hS := hasSum_sum (s := S) (fun i _ => hasSum_sum (s := S) (fun j _ => hterm i j))
    set q : ℕ → ℂ := fun n => ∑ i ∈ S, star (z i) * w n i
    have heq : (fun n => ∑ i ∈ S, ∑ j ∈ S, star (z i) * (c * (w n i * star (w n j))) * z j) =
        fun n => (((s⁻¹ * Complex.normSq (q n) : ℝ)) : ℂ) := by
      funext n
      have h1 : (∑ i ∈ S, ∑ j ∈ S, star (z i) * (c * (w n i * star (w n j))) * z j) =
          c * (q n * star (q n)) := by
        show _ = c * ((∑ i ∈ S, star (z i) * w n i) * star (∑ i ∈ S, star (z i) * w n i))
        rw [star_sum, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [star_mul', star_star]
        ring
      rw [h1, show star (q n) = (starRingEnd ℂ) (q n) from rfl, Complex.mul_conj, hc]
      push_cast; ring
    rw [heq] at hS
    have hsR : Summable (fun n => s⁻¹ * Complex.normSq (q n)) :=
      Complex.summable_ofReal.mp hS.summable
    have hval := hS.unique (Complex.hasSum_ofReal.mpr hsR.hasSum)
    rw [hval]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    exact tsum_nonneg (fun n => mul_nonneg (inv_nonneg.mpr hs0) (Complex.normSq_nonneg _))
  · have hb : ∀ i, HasSum (fun n => ‖w n i‖ ^ 2) (∑' n, ‖w n i‖ ^ 2) := fun i =>
      (Summable.of_nonneg_of_le (fun n => sq_nonneg _)
        (fun n => pow_le_pow_left₀ (norm_nonneg _) (norm_coord_le _ _) 2) hw).hasSum
    have hd := dsum_swap (fun p : ℕ × T => ‖w p.1 p.2‖ ^ 2) (fun _ => sq_nonneg _)
      (fun n => hasSum_normSq (w n)) hw.hasSum hb
    have hdiag : ∀ i, ((c • Mat w) i i).re = s⁻¹ * ∑' n, ‖w n i‖ ^ 2 := by
      intro i
      simp only [Matrix.smul_apply, smul_eq_mul, Mat]
      have h1 : (∑' n, w n i * star (w n i)) = (((∑' n, ‖w n i‖ ^ 2 : ℝ)) : ℂ) := by
        rw [Complex.ofReal_tsum]
        refine tsum_congr (fun n => ?_)
        rw [Complex.ofReal_pow, show star (w n i) = (starRingEnd ℂ) (w n i) from rfl,
          Complex.mul_conj']
      rw [h1, hc, ← Complex.ofReal_mul, Complex.ofReal_re]
    have h2 := hd.mul_left s⁻¹
    rw [inv_mul_cancel₀ hs] at h2
    simp_rw [hdiag]
    exact ⟨h2.summable, h2.tsum_eq⟩

lemma psi_Mat {I J E : Type} (Psi : Channel I E) (V : Hilbert I →L[ℂ] Hilbert (J × E))
    (hPsi : ∀ rho : State I,
      Psi.val rho.coefficients = traceFirst (boundedConjugation V rho.coefficients))
    (w : ℕ → Hilbert I) (hw : Summable (fun n => ‖w n‖ ^ 2)) (a b : E) :
    HasSum (fun n => ∑' j, (V (w n)) (j, a) * star ((V (w n)) (j, b))) (Psi.val (Mat w) a b) := by
  by_cases hs : (∑' n, ‖w n‖ ^ 2) = 0
  · have h0 := (hasSum_zero_iff_of_nonneg (fun n => sq_nonneg ‖w n‖)).mp (hs ▸ hw.hasSum)
    have hw0 : ∀ n, w n = 0 := fun n => by
      have := congrFun h0 n; simpa using this
    have hM : Mat w = 0 := by funext i j; simp [Mat, hw0]
    rw [hM, chan_zero]
    simpa [hw0] using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℂ)) 0)
  · set s := ∑' n, ‖w n‖ ^ 2 with hsdef
    set c : ℂ := ((s⁻¹ : ℝ) : ℂ) with hc
    have hsc : (s : ℂ) * c = 1 := by
      rw [hc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one]
    have hD := isDensity_mat w hw hs
    have h1 : Psi.val (c • Mat w) = traceFirst (boundedConjugation V (c • Mat w)) :=
      hPsi ⟨c • Mat w, hD⟩
    have hMs : Mat w = ((s : ℂ)) • (c • Mat w) := by
      rw [smul_smul, hsc, one_smul]
    have h2 : Psi.val (Mat w) = ((s:ℂ)) • Psi.val (c • Mat w) := by
      conv_lhs => rw [hMs]
      exact Psi.property.2.2.1 _ _ hD.1
    have h3 := (traceFirst_bconj_nuc V (matExp c w hw) a b).mul_left (s : ℂ)
    rw [h2, Matrix.smul_apply, smul_eq_mul, h1]
    have hfun : (fun n => ∑' j, (V (w n)) (j, a) * star ((V (w n)) (j, b))) =
        fun n => (s:ℂ) * ∑' j, (V ((matExp c w hw).left n)) (j, a) *
          star ((V ((matExp c w hw).right n)) (j, b)) := by
      funext n
      simp only [matExp, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [← tsum_mul_left]
      refine tsum_congr (fun j => ?_)
      rw [show (s:ℂ) * (c * (V (w n)) (j, a) * star ((V (w n)) (j, b))) =
        ((s:ℂ) * c) * ((V (w n)) (j, a) * star ((V (w n)) (j, b))) by ring, hsc, one_mul]
    rw [hfun]
    exact h3

/-! ## K3.7 polarization of a balanced expansion; the formula for `Psi X` -/

def wc {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (c : ℕ) (n : ℕ) : Hilbert I :=
  e.left n + Complex.I ^ c • e.right n

lemma wc_summable {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X)
    (hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖) (c : ℕ) : Summable (fun n => ‖wc e c n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (e.summable.mul_left 4)
  have h1 : ‖wc e c n‖ ≤ ‖e.left n‖ + ‖e.right n‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have h2 : ‖wc e c n‖ ^ 2 ≤ (‖e.left n‖ + ‖e.right n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [hbal n] at h2 ⊢
  nlinarith

lemma polar_split {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X)
    (hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖) :
    X = ∑ c ∈ Finset.range 4, (Complex.I ^ c / 4) • Mat (wc e c) := by
  funext i j
  rw [Matrix.sum_apply]
  have h := hasSum_sum (s := Finset.range 4) (fun c _ =>
    ((mat_coeff_summable (wc e c) (wc_summable e hbal c) i j).hasSum.mul_left (Complex.I ^ c / 4)))
  have hfun : (fun n => ∑ c ∈ Finset.range 4,
      Complex.I ^ c / 4 * (wc e c n i * star (wc e c n j))) =
      fun n => e.left n i * star (e.right n j) := by
    funext n
    rw [← polar4 (e.left n i) (e.right n i) (e.left n j) (e.right n j)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hw : ∀ t, (wc e c n) t = e.left n t + Complex.I ^ c * e.right n t := fun t => rfl
    rw [hw, hw]
  rw [hfun] at h
  rw [(coeff_hasSum e i j).unique h]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul]
  rfl

lemma psi_formula {I J E K : Type} (Psi : Channel I E) (V : Hilbert I →L[ℂ] Hilbert (J × E))
    (hPsi : ∀ rho : State I,
      Psi.val rho.coefficients = traceFirst (boundedConjugation V rho.coefficients))
    (A : K → (Hilbert I →L[ℂ] Hilbert E))
    (hG2 : ∀ (y z : Hilbert I) (a b : E), HasSum (fun k => (A k y) a * star ((A k z) b))
      (∑' j : J, (V y) (j, a) * star ((V z) (j, b))))
    {X : Matrix I I ℂ} (e : NuclearExpansion X) (hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖)
    (a b : E) :
    (∀ n, HasSum (fun k => (A k (e.left n)) a * star ((A k (e.right n)) b))
      (∑' k, (A k (e.left n)) a * star ((A k (e.right n)) b))) ∧
    HasSum (fun n => ∑' k, (A k (e.left n)) a * star ((A k (e.right n)) b)) (Psi.val X a b) := by
  have hk : ∀ n, HasSum (fun k => (A k (e.left n)) a * star ((A k (e.right n)) b))
      (∑ c ∈ Finset.range 4, (Complex.I ^ c / 4) *
        ∑' j : J, (V (wc e c n)) (j, a) * star ((V (wc e c n)) (j, b))) := by
    intro n
    have h := hasSum_sum (s := Finset.range 4) (fun c _ =>
      (hG2 (wc e c n) (wc e c n) a b).mul_left (Complex.I ^ c / 4))
    have hfun : (fun k => ∑ c ∈ Finset.range 4, Complex.I ^ c / 4 *
        ((A k (wc e c n)) a * star ((A k (wc e c n)) b))) =
        fun k => (A k (e.left n)) a * star ((A k (e.right n)) b) := by
      funext k
      rw [← polar4 ((A k (e.left n)) a) ((A k (e.right n)) a) ((A k (e.left n)) b)
        ((A k (e.right n)) b)]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      have hw : ∀ t, (A k (wc e c n)) t = (A k (e.left n)) t + Complex.I ^ c * (A k (e.right n)) t :=
        fun t => by rw [wc, map_add, map_smul]; rfl
      rw [hw, hw]
    rw [hfun] at h
    exact h
  refine ⟨fun n => (hk n).summable.hasSum, ?_⟩
  have hX := polar_split e hbal
  have hP : Psi.val X a b = ∑ c ∈ Finset.range 4,
      (Complex.I ^ c / 4) * Psi.val (Mat (wc e c)) a b := by
    conv_lhs => rw [hX]
    rw [chan_sum Psi 4 (fun c => Complex.I ^ c / 4) (fun c => Mat (wc e c))
      (fun c => tc_mat _ (wc_summable e hbal c)), Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hP]
  have h := hasSum_sum (s := Finset.range 4) (fun c _ =>
    (psi_Mat Psi V hPsi (wc e c) (wc_summable e hbal c) a b).mul_left (Complex.I ^ c / 4))
  have hfun : (fun n => ∑' k, (A k (e.left n)) a * star ((A k (e.right n)) b)) =
      fun n => ∑ c ∈ Finset.range 4, Complex.I ^ c / 4 *
        ∑' j : J, (V (wc e c n)) (j, a) * star ((V (wc e c n)) (j, b)) := by
    funext n; exact (hk n).tsum_eq
  rw [hfun]; exact h

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

lemma diff_hasSum {I J E K : Type} (Psi : Channel I E) (V : Hilbert I →L[ℂ] Hilbert (J × E))
    (hPsi : ∀ rho : State I,
      Psi.val rho.coefficients = traceFirst (boundedConjugation V rho.coefficients))
    (A : K → (Hilbert I →L[ℂ] Hilbert E))
    (hG2 : ∀ (y z : Hilbert I) (a b : E), HasSum (fun k => (A k y) a * star ((A k z) b))
      (∑' j : J, (V y) (j, a) * star ((V z) (j, b))))
    {X : Matrix I I ℂ} (e : NuclearExpansion X) (hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖)
    (F : Finset K) (a b : E) :
    HasSum (fun n => ∑' k : {k // k ∉ F}, (A k (e.left n)) a * star ((A k (e.right n)) b))
      ((Psi.val X - ∑ k ∈ F, conjugateCoeff (A k) X) a b) := by
  obtain ⟨hk, hn⟩ := psi_formula Psi V hPsi A hG2 e hbal a b
  have hc : HasSum (fun n => ∑ k ∈ F, (A k (e.left n)) a * star ((A k (e.right n)) b))
      (∑ k ∈ F, conjugateCoeff (A k) X a b) :=
    hasSum_sum (fun k _ => conj_hasSum (A k) e a b)
  have hd := hn.sub hc
  rw [Matrix.sub_apply, Matrix.sum_apply]
  have hfun : (fun n => ∑' k : {k // k ∉ F}, (A k (e.left n)) a * star ((A k (e.right n)) b)) =
      fun n => (∑' k, (A k (e.left n)) a * star ((A k (e.right n)) b)) -
        ∑ k ∈ F, (A k (e.left n)) a * star ((A k (e.right n)) b) := by
    funext n
    rw [← (hk n).summable.sum_add_tsum_subtype_compl F]
    ring
  rw [hfun]; exact hd

lemma amgm' (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

lemma diff_summ {I E K : Type} (A : K → (Hilbert I →L[ℂ] Hilbert E))
    (hA : ∀ u, HasSum (fun k => ‖A k u‖ ^ 2) (‖u‖ ^ 2))
    {X : Matrix I I ℂ} (e : NuclearExpansion X) (hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖)
    (F : Finset K) :
    Summable (fun p : ℕ × {k // k ∉ F} =>
      ‖A p.2.val (e.left p.1)‖ ^ 2 + ‖A p.2.val (e.right p.1)‖ ^ 2) ∧
    Summable (fun p : ℕ × {k // k ∉ F} =>
      ‖A p.2.val (e.left p.1)‖ * ‖A p.2.val (e.right p.1)‖) := by
  have hH : ∀ n, HasSum (fun k => ‖A k (e.left n)‖ ^ 2 + ‖A k (e.right n)‖ ^ 2)
      (‖e.left n‖ ^ 2 + ‖e.right n‖ ^ 2) := fun n => (hA _).add (hA _)
  have hbsum : Summable (fun n => ‖e.left n‖ ^ 2 + ‖e.right n‖ ^ 2) := by
    refine (e.summable.mul_left 2).congr (fun n => ?_)
    rw [hbal n]; ring
  have hHp : Summable (fun p : ℕ × K => ‖A p.2 (e.left p.1)‖ ^ 2 + ‖A p.2 (e.right p.1)‖ ^ 2) := by
    refine (summable_prod_of_nonneg (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))).2
      ⟨fun n => (hH n).summable, ?_⟩
    refine hbsum.congr (fun n => ?_)
    exact ((hH n).tsum_eq).symm
  have hemb : Function.Injective (fun p : ℕ × {k // k ∉ F} => ((p.1, p.2.val) : ℕ × K)) :=
    fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Subtype.ext h.2)
  have hHι := hHp.comp_injective hemb
  refine ⟨hHι, ?_⟩
  exact Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun p => amgm' _ _ (norm_nonneg _) (norm_nonneg _)) hHι

lemma diff_coeff {I J E K : Type} [Countable K] (Psi : Channel I E)
    (V : Hilbert I →L[ℂ] Hilbert (J × E))
    (hPsi : ∀ rho : State I,
      Psi.val rho.coefficients = traceFirst (boundedConjugation V rho.coefficients))
    (A : K → (Hilbert I →L[ℂ] Hilbert E))
    (hA : ∀ u, HasSum (fun k => ‖A k u‖ ^ 2) (‖u‖ ^ 2))
    (hG2 : ∀ (y z : Hilbert I) (a b : E), HasSum (fun k => (A k y) a * star ((A k z) b))
      (∑' j : J, (V y) (j, a) * star ((V z) (j, b))))
    {X : Matrix I I ℂ} (e : NuclearExpansion X) (hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖)
    (F : Finset K) (a b : E) :
    HasSum (fun p : ℕ × {k // k ∉ F} =>
      (A p.2.val (e.left p.1)) a * star ((A p.2.val (e.right p.1)) b))
      ((Psi.val X - ∑ k ∈ F, conjugateCoeff (A k) X) a b) := by
  have hg := (diff_summ A hA e hbal F).2
  have hs : Summable (fun p : ℕ × {k // k ∉ F} =>
      (A p.2.val (e.left p.1)) a * star ((A p.2.val (e.right p.1)) b)) :=
    Summable.of_norm_bounded hg (fun p => by
      rw [norm_mul, norm_star]
      exact mul_le_mul (norm_coord_le _ _) (norm_coord_le _ _) (norm_nonneg _) (norm_nonneg _))
  have h1 : HasSum (fun n => ∑' k : {k // k ∉ F}, (A k.val (e.left n)) a *
      star ((A k.val (e.right n)) b))
      (∑' p : ℕ × {k // k ∉ F}, (A p.2.val (e.left p.1)) a * star ((A p.2.val (e.right p.1)) b)) :=
    hs.hasSum.prod_fiberwise (fun n => (hs.prod_factor n).hasSum)
  have h2 := diff_hasSum Psi V hPsi A hG2 e hbal F a b
  have h3 := h1.unique h2
  rw [← h3]
  exact hs.hasSum

lemma diff_traceSize {I J E K : Type} [Countable K] (Psi : Channel I E)
    (V : Hilbert I →L[ℂ] Hilbert (J × E))
    (hPsi : ∀ rho : State I,
      Psi.val rho.coefficients = traceFirst (boundedConjugation V rho.coefficients))
    (A : K → (Hilbert I →L[ℂ] Hilbert E))
    (hA : ∀ u, HasSum (fun k => ‖A k u‖ ^ 2) (‖u‖ ^ 2))
    (hG2 : ∀ (y z : Hilbert I) (a b : E), HasSum (fun k => (A k y) a * star ((A k z) b))
      (∑' j : J, (V y) (j, a) * star ((V z) (j, b))))
    {X : Matrix I I ℂ} (e : NuclearExpansion X) (hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖)
    (F : Finset K) :
    traceSize (Psi.val X - ∑ k ∈ F, conjugateCoeff (A k) X) ≤
      ENNReal.ofReal (∑' n, ∑' k : {k // k ∉ F},
        (‖A k.val (e.left n)‖ ^ 2 + ‖A k.val (e.right n)‖ ^ 2)) := by
  obtain ⟨hHι, hg⟩ := diff_summ A hA e hbal F
  have hb := traceSize_le_of_countable (fun p : ℕ × {k // k ∉ F} => A p.2.val (e.left p.1))
    (fun p => A p.2.val (e.right p.1)) hg (diff_coeff Psi V hPsi A hA hG2 e hbal F)
  refine hb.2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hfib : HasSum (fun n => ∑' k : {k // k ∉ F},
      (‖A k.val (e.left n)‖ ^ 2 + ‖A k.val (e.right n)‖ ^ 2))
      (∑' p : ℕ × {k // k ∉ F}, (‖A p.2.val (e.left p.1)‖ ^ 2 + ‖A p.2.val (e.right p.1)‖ ^ 2)) :=
    hHι.hasSum.prod_fiberwise (fun n => (hHι.prod_factor n).hasSum)
  rw [hfib.tsum_eq]
  exact Summable.tsum_le_tsum (fun p => amgm' _ _ (norm_nonneg _) (norm_nonneg _)) hg hHι

/-! ## K3.10 the tails vanish -/

lemma tail_tendsto {K : Type} (H : ℕ → K → ℝ) (B : ℕ → ℝ) (hH0 : ∀ n k, 0 ≤ H n k)
    (hH : ∀ n, HasSum (H n) (B n)) (hB : Summable B) :
    Tendsto (fun F : Finset K => ∑' n, ∑' k : {k // k ∉ F}, H n k.val) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter (Finset K)))
    (f := fun F n => ∑' k : {k // k ∉ F}, H n k.val) (g := fun _ => (0:ℝ)) (bound := B) hB
    (fun n => tendsto_tsum_compl_atTop_zero (H n))
    (Eventually.of_forall (fun F n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (g := fun k : {k // k ∉ F} => H n k.val)
        (fun k => hH0 n k.val)),
        ← (hH n).tsum_eq]
      exact Summable.tsum_subtype_le (H n) {k | k ∉ F} (hH0 n) (hH n).summable))
  simpa using h

/-! ## K3 main: trace-norm convergence of the Kraus series -/

theorem k3 {I J E K : Type} [Countable K] (Psi : Channel I E)
    (V : Hilbert I →L[ℂ] Hilbert (J × E))
    (hPsi : ∀ rho : State I,
      Psi.val rho.coefficients = traceFirst (boundedConjugation V rho.coefficients))
    (A : K → (Hilbert I →L[ℂ] Hilbert E))
    (hA : ∀ u, HasSum (fun k => ‖A k u‖ ^ 2) (‖u‖ ^ 2))
    (hG2 : ∀ (y z : Hilbert I) (a b : E), HasSum (fun k => (A k y) a * star ((A k z) b))
      (∑' j : J, (V y) (j, a) * star ((V z) (j, b))))
    (X : Matrix I I ℂ) (hX : IsTraceClass X) :
    Tendsto (fun F : Finset K =>
      traceSize (Psi.val X - ∑ k ∈ F, conjugateCoeff (A k) X)) atTop (𝓝 0) := by
  obtain ⟨e0⟩ := hX
  obtain ⟨e, he⟩ := balance e0
  have hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖ := fun n =>
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ((he n).1.trans (he n).2.symm)
  have hbsum : Summable (fun n => ‖e.left n‖ ^ 2 + ‖e.right n‖ ^ 2) := by
    refine (e.summable.mul_left 2).congr (fun n => ?_)
    rw [hbal n]; ring
  have hT := tail_tendsto (fun n k => ‖A k (e.left n)‖ ^ 2 + ‖A k (e.right n)‖ ^ 2)
    (fun n => ‖e.left n‖ ^ 2 + ‖e.right n‖ ^ 2) (fun _ _ => by positivity)
    (fun n => (hA _).add (hA _)) hbsum
  have hT' := (ENNReal.tendsto_ofReal hT)
  rw [ENNReal.ofReal_zero] at hT'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT'
    (fun _ => by simp) (fun F => diff_traceSize Psi V hPsi A hA hG2 e hbal F)

end P45K


noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology
open Filter

namespace P45A3
noncomputable local instance (priority := 1100) scH_nacg_4 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_4 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_4 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_4 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_4 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_4 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
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
noncomputable local instance (priority := 1100) scA_bcadd_4 (X : Type) : ContinuousAdd (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_btag_4 (X : Type) : IsTopologicalAddGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bccs_4 (X : Type) : ContinuousConstSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcs_4 (X : Type) : ContinuousSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bt2_4 (X : Type) : T2Space (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_badd_4 (X : Type) : Add (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bsmul_4 (X : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcladd_4 (X Y : Type) : Add (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsub_4 (X Y : Type) : Sub (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsmul_4 (X Y : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclmul_4 (X : Type) : Mul (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bclfun_4 (X Y : Type) : FunLike (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) (QAlgorithms.RealRegisters.Hilbert X) (QAlgorithms.RealRegisters.Hilbert Y) := inferInstance

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

lemma hG2_of {I J E K : Type} {Phi : Channel I J} {Psi : Channel I E}
    (V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × E))
    (hV : ∀ rho : State I,
      Phi.val rho.coefficients = traceSecond (boundedConjugation V.toContinuousLinearMap rho.coefficients) ∧
      Psi.val rho.coefficients = traceFirst (boundedConjugation V.toContinuousLinearMap rho.coefficients))
    (psi : K → Hilbert J)
    (hpsi : ∀ x, HasSum (fun k => ‖inner ℂ (psi k) x‖ ^ 2)
      (inner ℂ x (outputProjection Phi.val x)).re)
    (y z : Hilbert I) (a b : E) :
    HasSum (fun k => (((P45D.braL (E := E) (psi k)).comp V.toContinuousLinearMap) y) a *
        star ((((P45D.braL (E := E) (psi k)).comp V.toContinuousLinearMap) z) b))
      (∑' j : J, (V.toContinuousLinearMap y) (j, a) * star ((V.toContinuousLinearMap z) (j, b))) := by
  have hx := P45D.outputProjection_fix Phi.val _ (P45D.slice_in_output V hV y a)
  have hy := P45D.outputProjection_fix Phi.val _ (P45D.slice_in_output V hV z b)
  have h := P45K.frame_polar (outputProjection Phi.val) psi hpsi _ _ hx hy
  have hval : (∑' j : J, (V.toContinuousLinearMap y) (j, a) *
      star ((V.toContinuousLinearMap z) (j, b))) =
      inner ℂ (P45D.sliceV b (V z)) (P45D.sliceV a (V y)) := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr (fun j => ?_)
    simp [RCLike.inner_apply, mul_comm]
  rw [hval]
  exact h


end P45A3

section N2C

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology

attribute [local instance] Classical.propDecidable

namespace P45N2C
noncomputable local instance (priority := 1100) scH_nacg_5 (X : Type) : NormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ips_5 (X : Type) : InnerProductSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_cs_5 (X : Type) : CompleteSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acg_5 (X : Type) : AddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_acm_5 (X : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_mod_5 (X : Type) : Module ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_ns_5 (X : Type) : NormedSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_5 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_am_5 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_5 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_5 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
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
open P45D

/-- The rank-one operator `x ↦ ⟪w, x⟫ • φ` between two coordinate spaces. -/
def rk2 {I E : Type} (φ : Hilbert E) (w : Hilbert I) : Hilbert I →L[ℂ] Hilbert E :=
  (innerSL ℂ w).smulRight φ

lemma rk2_apply {I E : Type} (φ : Hilbert E) (w x : Hilbert I) : rk2 φ w x = inner ℂ w x • φ := rfl

lemma fiber_inner {T A : Type} (y z : Hilbert (T × A)) :
    HasSum (fun a => inner ℂ (sliceV a y) (sliceV a z)) (inner ℂ y z) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) y z
  have h' : HasSum ((fun p : T × A => inner ℂ (y p) (z p)) ∘ Prod.swap) (inner ℂ y z) :=
    (Equiv.prodComm A T).hasSum_iff.mpr h
  exact h'.prod_fiberwise (fun a => by simpa using lp.hasSum_inner (𝕜 := ℂ) (sliceV a y) (sliceV a z))

/-- Summing the bra-sliced norms over a rank-one resolution of `B` gives `⟪y, (B ⊗ 1) y⟫`. -/
lemma bra_sum {J E K : Type} (B : Hilbert J →L[ℂ] Hilbert J) (psi : K → Hilbert J)
    (hpsi : ∀ z, HasSum (fun j => ‖inner ℂ (psi j) z‖ ^ 2) (inner ℂ z (B z)).re)
    (y : Hilbert (J × E)) :
    HasSum (fun j => ‖braL (E := E) (psi j) y‖ ^ 2) (inner ℂ y (ampL (E := E) B y)).re := by
  have hs : HasSum (fun e : E => (inner ℂ (sliceV e y) (B (sliceV e y))).re)
      (inner ℂ y (ampL (E := E) B y)).re := by
    have h := (fiber_inner y (ampL (E := E) B y)).mapL Complex.reCLM
    simp only [Complex.reCLM_apply] at h
    have hf : (fun e : E => (inner ℂ (sliceV e y) (sliceV e (ampL (E := E) B y))).re) =
        fun e => (inner ℂ (sliceV e y) (B (sliceV e y))).re := by
      funext e
      rw [ampL_apply, slice_ampV]
    rw [hf] at h
    exact h
  refine dsum_swap (fun p : E × K => ‖inner ℂ (psi p.2) (sliceV p.1 y)‖ ^ 2)
    (fun _ => sq_nonneg _) (fun e => hpsi (sliceV e y)) hs (fun j => ?_)
  exact hasSum_normSq (braV (psi j) y)

lemma re_inner_rk {I : Type} (w x : Hilbert I) :
    (inner ℂ x (P45D.rk w w x)).re = ‖inner ℂ w x‖ ^ 2 := by
  have e : inner ℂ x w = (starRingEnd ℂ) (inner ℂ w x) := (inner_conj_symm x w).symm
  rw [P45D.rk_apply, inner_smul_right, e, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- N2c core: if `W† (B ⊗ 1) W = |w⟩⟨w|` and `psi` resolves `B` into rank-one forms, every
complement Kraus operator `(⟨psi_j| ⊗ 1) W` is `|φ_j⟩⟨w|` with `Σ ‖φ_j‖² = 1`. -/
theorem kraus_rankone {I J E K : Type} (W : Hilbert I →L[ℂ] Hilbert (J × E))
    (B : Hilbert J →L[ℂ] Hilbert J) (psi : K → Hilbert J)
    (hpsi : ∀ z, HasSum (fun j => ‖inner ℂ (psi j) z‖ ^ 2) (inner ℂ z (B z)).re)
    (w : Hilbert I) (hw0 : w ≠ 0)
    (hdual : (ContinuousLinearMap.adjoint W).comp ((ampL (E := E) B).comp W) = P45D.rk w w) :
    ∃ φ : K → Hilbert E, HasSum (fun j => ‖φ j‖ ^ 2) 1 ∧
      ∀ j, (braL (E := E) (psi j)).comp W = rk2 (φ j) w := by
  have hform : ∀ x, HasSum (fun j => ‖braL (E := E) (psi j) (W x)‖ ^ 2) (‖inner ℂ w x‖ ^ 2) := by
    intro x
    have h := bra_sum B psi hpsi (W x)
    have e : (inner ℂ (W x) (ampL (E := E) B (W x))).re = ‖inner ℂ w x‖ ^ 2 := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      have := congrArg (fun T : Hilbert I →L[ℂ] Hilbert I => T x) hdual
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this, re_inner_rk]
    rw [e] at h
    exact h
  have hker : ∀ j x, inner ℂ w x = 0 → braL (E := E) (psi j) (W x) = 0 := by
    intro j x hx
    have h := le_hasSum (hform x) j (fun _ _ => sq_nonneg _)
    rw [hx, norm_zero] at h
    have h0 : ‖braL (E := E) (psi j) (W x)‖ ^ 2 = 0 :=
      le_antisymm (by simpa using h) (sq_nonneg _)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  have hww : inner ℂ w w = ((‖w‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K w
  have hwc : ((‖w‖ : ℂ)) ^ 2 ≠ 0 := by
    have : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hwn.ne'
    exact pow_ne_zero 2 this
  refine ⟨fun j => (((‖w‖ : ℂ)) ^ 2)⁻¹ • braL (E := E) (psi j) (W w), ?_, fun j => ?_⟩
  · have h := (hform w).div_const (‖w‖ ^ 4)
    have h1 : ‖inner ℂ w w‖ ^ 2 / ‖w‖ ^ 4 = 1 := by
      rw [hww, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwn]
      field_simp
    rw [h1] at h
    have hf : (fun j => ‖braL (E := E) (psi j) (W w)‖ ^ 2 / ‖w‖ ^ 4) =
        fun j => ‖(((‖w‖ : ℂ)) ^ 2)⁻¹ • braL (E := E) (psi j) (W w)‖ ^ 2 := by
      funext j
      rw [norm_smul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwn]
      field_simp
    rw [hf] at h
    exact h
  · refine ContinuousLinearMap.ext fun x => ?_
    set c : ℂ := inner ℂ w x / ((‖w‖ : ℂ)) ^ 2 with hc
    have horth : inner ℂ w (x - c • w) = 0 := by
      rw [inner_sub_right, inner_smul_right, hww, hc, div_mul_cancel₀ _ hwc, sub_self]
    have hx : x = (x - c • w) + c • w := by abel
    rw [ContinuousLinearMap.comp_apply, rk2_apply, hx, map_add, map_add,
      hker j _ horth, zero_add, map_smul, map_smul, smul_smul, inner_add_right, horth, zero_add,
      inner_smul_right, hww, mul_assoc, mul_inv_cancel₀ hwc, mul_one]

end P45N2C

end

end N2C

section N2K

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate Topology

attribute [local instance] Classical.propDecidable

namespace P45N2K
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
noncomputable local instance (priority := 1100) scA_bcadd_6 (X : Type) : ContinuousAdd (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_btag_6 (X : Type) : IsTopologicalAddGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bccs_6 (X : Type) : ContinuousConstSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcs_6 (X : Type) : ContinuousSMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bt2_6 (X : Type) : T2Space (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_badd_6 (X : Type) : Add (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bsmul_6 (X : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bcladd_6 (X Y : Type) : Add (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsub_6 (X Y : Type) : Sub (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclsmul_6 (X Y : Type) : SMul ℂ (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scA_bclmul_6 (X : Type) : Mul (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scA_bclfun_6 (X Y : Type) : FunLike (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) (QAlgorithms.RealRegisters.Hilbert X) (QAlgorithms.RealRegisters.Hilbert Y) := inferInstance

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass traceSize rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator IsKrausRepresentation)
open QAlgorithms.Papers.Independent.Gap48.P45 (operatorRank channelDual outputProjection
  rankMultiplicity BoundIndex)


/-- N2K: a resolution of the output projection by positive `B_i` whose duals are the
rank-one projectors `|w_i⟩⟨w_i|` makes the complement a Kraus channel with operators
`|φ_ij⟩⟨w_i|`, `Σ_j ‖φ_ij‖² = 1`, indexed by `L × BoundIndex m_1`. -/
theorem n2k {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (B : L → (Hilbert J →L[ℂ] Hilbert J))
    (hres : ∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
      (inner ℂ x (outputProjection Phi.val x)).re)
    (hpsi0 : ∀ i, ∃ psi : BoundIndex (rankMultiplicity Phi.val 1) → Hilbert J,
      ∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B i x)).re)
    (w : L → Hilbert I) (hw0 : ∀ i, w i ≠ 0)
    (hdual : ∀ i, channelDual Phi.val (B i) = (innerSL ℂ (w i)).smulRight (w i)) :
    ∃ phi : L → BoundIndex (rankMultiplicity Phi.val 1) → Hilbert E,
      (∀ i, HasSum (fun j => ‖phi i j‖ ^ 2) 1) ∧
      IsKrausRepresentation Psi.val
        (fun p : L × BoundIndex (rankMultiplicity Phi.val 1) =>
          ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) : Hilbert I →L[ℂ] Hilbert E)) := by
  have hComp' := hComp
  obtain ⟨V, hV⟩ := hComp'
  choose psi hpsi using hpsi0



  have hdual' : ∀ i, (ContinuousLinearMap.adjoint V.toContinuousLinearMap).comp
      ((P45D.ampL (E := E) (B i)).comp V.toContinuousLinearMap) = P45D.rk (w i) (w i) :=
    fun i => (P45D.aDual Phi Psi V hV (B i)).symm.trans (hdual i)
  choose phi hphi hA using fun i => P45N2C.kraus_rankone V.toContinuousLinearMap (B i) (psi i)
    (hpsi i) (w i) (hw0 i) (hdual' i)
  let psi' : L × BoundIndex (rankMultiplicity Phi.val 1) → Hilbert J := fun p => psi p.1 p.2
  have hpsi' : ∀ x, HasSum (fun p => ‖inner ℂ (psi' p) x‖ ^ 2)
      (inner ℂ x (outputProjection Phi.val x)).re := fun x =>
    P45D.joint1 (fun p => ‖inner ℂ (psi p.1 p.2) x‖ ^ 2) (fun _ => sq_nonneg _)
      (fun i => hpsi i x) (hres x)
  have hK : IsKrausRepresentation Psi.val
      (fun p => (P45D.braL (E := E) (psi' p)).comp V.toContinuousLinearMap) :=
    ⟨fun x => P45D.kraus_first V hV psi' hpsi' x, fun X hX =>
      P45K.k3 Psi V.toContinuousLinearMap (fun rho => (hV rho).2) _
        (P45D.kraus_norm V (outputProjection Phi.val) psi' hpsi'
          (fun u e => P45D.outputProjection_fix _ _ (P45D.slice_in_output V hV u e)))
        (P45A3.hG2_of V hV psi' hpsi') X hX⟩
  have hfam : (fun p : L × BoundIndex (rankMultiplicity Phi.val 1) =>
      (P45D.braL (E := E) (psi' p)).comp V.toContinuousLinearMap) =
      fun p => ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) : Hilbert I →L[ℂ] Hilbert E) :=
    funext fun p => hA p.1 p.2
  exact ⟨phi, hphi, hfam ▸ hK⟩

end P45N2K

end

end N2K

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
theorem solution {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (B : L → (Hilbert J →L[ℂ] Hilbert J))
    (hres : ∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
      (inner ℂ x (outputProjection Phi.val x)).re)
    (hpsi0 : ∀ i, ∃ psi : BoundIndex (rankMultiplicity Phi.val 1) → Hilbert J,
      ∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B i x)).re)
    (w : L → Hilbert I) (hw0 : ∀ i, w i ≠ 0)
    (hdual : ∀ i, channelDual Phi.val (B i) = (innerSL ℂ (w i)).smulRight (w i)) :
    ∃ phi : L → BoundIndex (rankMultiplicity Phi.val 1) → Hilbert E,
      (∀ i, HasSum (fun j => ‖phi i j‖ ^ 2) 1) ∧
      IsKrausRepresentation Psi.val
        (fun p : L × BoundIndex (rankMultiplicity Phi.val 1) =>
          ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) : Hilbert I →L[ℂ] Hilbert E)) := by
  exact P45N2K.n2k Phi Psi hComp B hres hpsi0 w hw0 hdual

end

end ChildRoot
