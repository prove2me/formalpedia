-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.petz_identity_dual_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:10:01.288801+00:00
-- url     : https://prove2.me/submissions/cb666ec6-a96a-4976-98f0-46a689700bea

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

lemma reindexV_apply {T U : Type} (e : T ≃ U) (x : Hilbert U) (t : T) :
    reindexV e x t = x (e t) := rfl

lemma norm_reindexV {T U : Type} (e : T ≃ U) (x : Hilbert U) : ‖reindexV e x‖ = ‖x‖ := by
  have h1 := (hasSum_normSq (reindexV e x)).tsum_eq
  have h2 := (hasSum_normSq x).tsum_eq
  have h3 : (∑' t, ‖reindexV e x t‖ ^ 2) = ∑' u, ‖x u‖ ^ 2 :=
    e.tsum_eq (fun u => ‖x u‖ ^ 2)
  have h : ‖reindexV e x‖ ^ 2 = ‖x‖ ^ 2 := by rw [← h1, ← h2, h3]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma isTraceClass_reindex {T U : Type} (e : T ≃ U) {Y : Matrix U U ℂ} (hY : IsTraceClass Y) :
    IsTraceClass (Y.submatrix e e) := by
  obtain ⟨E⟩ := hY
  refine ⟨⟨fun n => reindexV e (E.left n), fun n => reindexV e (E.right n), ?_, ?_⟩⟩
  · simpa only [norm_reindexV] using E.summable
  · intro i j
    simp only [Matrix.submatrix_apply, reindexV_apply]
    exact E.coefficients (e i) (e j)

lemma isDensity_reindex {T U : Type} (e : T ≃ U) {Y : Matrix U U ℂ} (hY : IsDensity Y) :
    IsDensity (Y.submatrix e e) := by
  obtain ⟨htc, hq, hsum, htr⟩ := hY
  refine ⟨isTraceClass_reindex e htc, fun s z => ?_, ?_, ?_⟩
  · have h := hq (s.map e.toEmbedding) (fun u => z (e.symm u))
    simp only [Finset.sum_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at h
    simpa only [Matrix.submatrix_apply] using h
  · exact (e.summable_iff (f := fun u => (Y u u).re)).mpr hsum
  · simp only [Matrix.submatrix_apply]
    rw [e.tsum_eq (fun u => (Y u u).re)]
    exact htr

lemma chan_density {I J : Type} (Psi : Matrix I I ℂ → Matrix J J ℂ) (hPsi : IsTraceClassChannel Psi)
    (X : Matrix I I ℂ) (hX : IsDensity X) : IsDensity (Psi X) := by
  let e : I × Fin 1 ≃ I := Equiv.prodUnique I (Fin 1)
  have hX1 : IsDensity (X.submatrix e e) := isDensity_reindex e hX
  have hY := hPsi.2.2.2 1 ⟨X.submatrix e e, hX1⟩
  have hT : tensorApply Psi (X.submatrix e e) = (Psi X).submatrix
      (Equiv.prodUnique J (Fin 1)) (Equiv.prodUnique J (Fin 1)) := by
    funext p q
    rfl
  rw [hT] at hY
  have h := isDensity_reindex (Equiv.prodUnique J (Fin 1)).symm hY
  have h2 : ((Psi X).submatrix (Equiv.prodUnique J (Fin 1)) (Equiv.prodUnique J (Fin 1))).submatrix
      (Equiv.prodUnique J (Fin 1)).symm (Equiv.prodUnique J (Fin 1)).symm = Psi X := by
    funext i j
    simp
  rwa [h2] at h

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


/-! ## Trace preservation on all of trace class -/




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

lemma inner_eq_tsum' {T : Type} (x y : Hilbert T) : inner ℂ x y = ∑' k, star (x k) * y k := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr (fun k => ?_)
  simp [RCLike.inner_apply, mul_comm]


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

/-- Expansion from coefficientwise HasSum. -/
def mkExp {I : Type} {X : Matrix I I ℂ} (u v : ℕ → Hilbert I)
    (hs : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hX : ∀ i j, HasSum (fun n => u n i * star (v n j)) (X i j)) : NuclearExpansion X where
  left := u
  right := v
  summable := hs
  coefficients := fun i j => (hX i j).tsum_eq.symm


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

lemma tc_rk {T : Type} (u v : Hilbert T) : IsTraceClass (operatorCoeff (rk u v)) := by
  refine ⟨mkExp (fun n => if n = 0 then u else 0) (fun n => if n = 0 then v else 0) ?_ ?_⟩
  · have h : (fun n : ℕ => ‖(if n = 0 then u else 0 : Hilbert T)‖ *
        ‖(if n = 0 then v else 0 : Hilbert T)‖) = fun n => if n = 0 then ‖u‖ * ‖v‖ else 0 := by
      funext n; split_ifs <;> simp
    rw [h]; exact (hasSum_ite_eq 0 _).summable
  · intro i j
    have h : (fun n : ℕ => (if n = 0 then u else 0 : Hilbert T) i *
        star ((if n = 0 then v else 0 : Hilbert T) j)) =
        fun n => if n = 0 then u i * star (v j) else 0 := by
      funext n; split_ifs <;> simp
    rw [h, coeff_rk]; exact hasSum_ite_eq 0 _

lemma inner_rk_self {T : Type} (u x : Hilbert T) :
    inner ℂ (rk u u x) x = ((‖inner ℂ u x‖ ^ 2 : ℝ) : ℂ) := by
  rw [rk_apply, inner_smul_left, Complex.conj_mul']
  push_cast; ring

lemma inner_sq_self {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {t P : E →L[ℂ] E} (ht : ContinuousLinearMap.adjoint t = t) (htt : t * t = P) (x : E) :
    inner ℂ (P x) x = ((‖t x‖ ^ 2 : ℝ) : ℂ) := by
  rw [← htt]
  change inner ℂ (t (t x)) x = _
  rw [show t (t x) = ContinuousLinearMap.adjoint t (t x) by rw [ht],
    ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma isPos_of_real {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (f : E → ℝ) (hf : ∀ x, inner ℂ (T x) x = ((f x : ℝ) : ℂ))
    (h0 : ∀ x, 0 ≤ f x) : T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  rw [hf]
  have h1 := h0 x
  generalize f x = r at h1 ⊢
  exact ⟨by simp, by simpa using h1⟩

lemma pos_re {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {T : E →L[ℂ] E} (hT : T.IsPositive) (x : E) : 0 ≤ (inner ℂ (T x) x).re := by
  have := ((ContinuousLinearMap.isPositive_iff_complex T).mp hT x).2
  simpa using this

lemma chan_pos_of {I J : Type} (Phi : Channel I J) (S : Hilbert I →L[ℂ] Hilbert I)
    (hS : S.IsPositive) (htc : IsTraceClass (operatorCoeff S)) (τ : ℝ) (hτ : 0 < τ)
    (hd : HasSum (fun k => (operatorCoeff S k k).re) τ) :
    (boundedOperator (Phi.val (operatorCoeff S))).IsPositive := by
  set D : Matrix I I ℂ := ((τ⁻¹ : ℝ) : ℂ) • operatorCoeff S with hDdef
  have hD : IsDensity D := by
    refine ⟨tc_smul _ htc, fun s z => ?_, ?_, ?_⟩
    · have hf := form_eq S s id z
      simp only [id] at hf
      have hsum : (∑ i ∈ s, ∑ j ∈ s, star (z i) * D i j * z j) =
          ((τ⁻¹ : ℝ) : ℂ) * ∑ i ∈ s, ∑ j ∈ s, star (z i) * operatorCoeff S i j * z j := by
        simp only [hDdef, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      set v : Hilbert I := ∑ q ∈ s, z q • (lp.single 2 q (1:ℂ) : Hilbert I)
      obtain ⟨hre, hnn⟩ := (ContinuousLinearMap.isPositive_iff_complex S).mp hS v
      set r : ℝ := (inner ℂ (S v) v).re with hr
      have h2 : inner ℂ (S v) v = ((r : ℝ) : ℂ) := by simpa using hre.symm
      have hv : inner ℂ v (S v) = ((r : ℝ) : ℂ) := by
        rw [← inner_conj_symm, h2, Complex.conj_ofReal]
      rw [hsum, hf, hv, ← Complex.ofReal_mul]
      refine ⟨Complex.ofReal_im _, ?_⟩
      rw [Complex.ofReal_re]
      exact mul_nonneg (inv_nonneg.mpr hτ.le) (by simpa using hnn)
    · have h := hd.mul_left τ⁻¹
      refine h.summable.congr (fun k => ?_)
      simp [hDdef, Matrix.smul_apply]
    · have h := hd.mul_left τ⁻¹
      rw [inv_mul_cancel₀ hτ.ne'] at h
      rw [← h.tsum_eq]
      refine tsum_congr (fun k => ?_)
      simp [hDdef, Matrix.smul_apply]
  have hPD := chan_density Phi.val Phi.property D hD
  have hpos := bO_pos ⟨Phi.val D, hPD⟩
  have hS' : operatorCoeff S = ((τ : ℝ) : ℂ) • D := by
    rw [hDdef, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hτ.ne', Complex.ofReal_one,
      one_smul]
  have hPhi : Phi.val (operatorCoeff S) = ((τ : ℝ) : ℂ) • Phi.val D := by
    rw [hS']; exact Phi.property.2.2.1 _ _ hD.1
  have hbO : boundedOperator (Phi.val (operatorCoeff S)) =
      ((τ : ℝ) : ℂ) • boundedOperator (Phi.val D) := by
    rw [hPhi]; apply bO_eq; rw [coeff_smul, coeff_bO hPD.1]
  rw [hbO]
  exact hpos.smul_of_nonneg (by exact_mod_cast hτ.le)

lemma rank_bound {I J : Type} (Phi : Channel I J) (sigma : State I)
    (s : Hilbert I →L[ℂ] Hilbert I)
    (hs : ContinuousLinearMap.adjoint s = s) (hss : s * s = boundedOperator sigma.coefficients)
    (w : Hilbert I) :
    0 ≤ boundedOperator (Phi.val (operatorCoeff (rk (s w) (s w)))) ∧
    ∀ x, (inner ℂ x (boundedOperator (Phi.val (operatorCoeff (rk (s w) (s w)))) x)).re ≤
      (‖w‖ ^ 2 + ‖s w‖ ^ 2 + 1) *
        (inner ℂ x (boundedOperator (Phi.val sigma.coefficients) x)).re := by
  set u := s w with hu
  have hY := tc_rk u u
  have hσ := sigma.density.1
  set c : ℝ := ‖w‖ ^ 2 + ‖u‖ ^ 2 + 1 with hc
  have hrkpos : (rk u u).IsPositive := by
    exact isPos_of_real _ (fun x => ‖inner ℂ u x‖ ^ 2) (fun x => inner_rk_self u x)
      (fun x => sq_nonneg _)
  have hdiagY : HasSum (fun k => (operatorCoeff (rk u u) k k).re) (‖u‖ ^ 2) := by
    convert hasSum_normSq u using 1
    funext k
    rw [coeff_rk, show star (u k) = (starRingEnd ℂ) (u k) from rfl, Complex.mul_conj',
      ← Complex.ofReal_pow, Complex.ofReal_re]
  constructor
  · rw [ContinuousLinearMap.nonneg_iff_isPositive]
    by_cases hu0 : u = 0
    · have h0 : operatorCoeff (rk u u) = 0 := by
        funext i j; simp [coeff_rk, hu0]
      rw [h0, chan_zero, bO_eq (show operatorCoeff (0 : Hilbert J →L[ℂ] Hilbert J) = 0 by
        funext i j; simp [operatorCoeff])]
      exact ContinuousLinearMap.isPositive_zero
    · exact chan_pos_of Phi (rk u u) hrkpos hY (‖u‖ ^ 2) (by positivity) hdiagY
  · intro x
    set S2 : Hilbert I →L[ℂ] Hilbert I := ((c : ℂ)) • boundedOperator sigma.coefficients - rk u u
      with hS2
    have hin : ∀ y, inner ℂ (S2 y) y = (((c * ‖s y‖ ^ 2 - ‖inner ℂ u y‖ ^ 2) : ℝ) : ℂ) := by
      intro y
      rw [hS2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
        inner_smul_left, inner_sq_self hs hss, inner_rk_self, Complex.conj_ofReal]
      push_cast; ring
    have hS2pos : S2.IsPositive := by
      refine isPos_of_real _ _ hin (fun y => ?_)
      have h1 : ‖inner ℂ u y‖ ≤ ‖w‖ * ‖s y‖ := by
        rw [hu, show s w = ContinuousLinearMap.adjoint s w by rw [hs],
          ContinuousLinearMap.adjoint_inner_left]
        exact norm_inner_le_norm _ _
      have h2 : ‖inner ℂ u y‖ ^ 2 ≤ ‖w‖ ^ 2 * ‖s y‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : ‖w‖ ^ 2 ≤ c := by rw [hc]; nlinarith [sq_nonneg ‖u‖]
      nlinarith [sq_nonneg ‖s y‖]
    have hcS2 : operatorCoeff S2 = ((c : ℂ)) • sigma.coefficients - operatorCoeff (rk u u) := by
      rw [hS2, coeff_sub, coeff_smul, coeff_bO hσ]
    have htc2 : IsTraceClass (operatorCoeff S2) := by
      rw [hcS2, sub_eq_add_neg, ← neg_one_smul ℂ (operatorCoeff (rk u u))]
      exact tc_add (tc_smul _ hσ) (tc_smul _ hY)
    have hσd : HasSum (fun k => (sigma.coefficients k k).re) 1 := by
      obtain ⟨_, _, hsm, htr⟩ := sigma.density
      rw [← htr]; exact hsm.hasSum
    have hdiag2 : HasSum (fun k => (operatorCoeff S2 k k).re) (c * 1 - ‖u‖ ^ 2) := by
      have h := (hσd.mul_left c).sub hdiagY
      have hfun : (fun k => (operatorCoeff S2 k k).re) =
          fun k => c * (sigma.coefficients k k).re - (operatorCoeff (rk u u) k k).re := by
        funext k
        rw [hcS2]
        simp [Matrix.sub_apply, Matrix.smul_apply]
      rw [hfun]; exact h
    have hpos2 := chan_pos_of Phi S2 hS2pos htc2 (c * 1 - ‖u‖ ^ 2)
      (by rw [hc]; nlinarith [sq_nonneg ‖w‖]) hdiag2
    have hPhi2 : Phi.val (operatorCoeff S2) =
        ((c : ℂ)) • Phi.val sigma.coefficients - Phi.val (operatorCoeff (rk u u)) := by
      rw [hcS2, sub_eq_add_neg, ← neg_one_smul ℂ (operatorCoeff (rk u u)),
        Phi.property.2.1 _ _ (tc_smul _ hσ) (tc_smul _ hY), Phi.property.2.2.1 _ _ hσ,
        Phi.property.2.2.1 _ _ hY, neg_one_smul, ← sub_eq_add_neg]
    have hbO2 : boundedOperator (Phi.val (operatorCoeff S2)) =
        ((c : ℂ)) • boundedOperator (Phi.val sigma.coefficients) -
          boundedOperator (Phi.val (operatorCoeff (rk u u))) := by
      rw [hPhi2]; apply bO_eq
      rw [coeff_sub, coeff_smul, coeff_bO (Phi.property.1 _ hσ), coeff_bO (Phi.property.1 _ hY)]
    have h := pos_re hpos2 x
    rw [hbO2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
      inner_smul_left, Complex.conj_ofReal, Complex.sub_re, Complex.re_ofReal_mul] at h
    rw [← inner_conj_symm, Complex.conj_re, ← inner_conj_symm x, Complex.conj_re]
    linarith

/-! ## s3: C1 part 2, Theta(Phi sigma) = sigma -/

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
lemma good_sum {I J : Type} (Phi : Channel I J) (sigma : State I) (m : ℕ) (c : ℕ → ℂ)
    (a : ℕ → Hilbert I) :
    ∃ B : Hilbert J →L[ℂ] Hilbert J,
      (coefficientSupportProjection (Phi.val sigma.coefficients)).comp
          (B.comp (coefficientSupportProjection (Phi.val sigma.coefficients))) = B ∧
      (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients))).comp
          (B.comp (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)))) =
        boundedOperator (Phi.val (operatorCoeff
          ((positiveSquareRoot (boundedOperator sigma.coefficients)).comp
            ((∑ k ∈ Finset.range m, c k • rk (a k) (a k)).comp
              (positiveSquareRoot (boundedOperator sigma.coefficients)))))) := by
  set rho : State J := ⟨Phi.val sigma.coefficients,
    chan_density Phi.val Phi.property _ sigma.density⟩ with hrho
  obtain ⟨ht, htt, _⟩ := sqrt_state rho
  obtain ⟨hs, hss, _⟩ := sqrt_state sigma
  set t := positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) with htdef
  set s := positiveSquareRoot (boundedOperator sigma.coefficients) with hsdef
  set P := boundedOperator (Phi.val sigma.coefficients) with hPdef
  have hk : ∀ k, ∃ B : Hilbert J →L[ℂ] Hilbert J,
      ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection).comp
          (B.comp ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection)) = B ∧
      t.comp (B.comp t) = boundedOperator (Phi.val (operatorCoeff (rk (s (a k)) (s (a k))))) := by
    intro k
    obtain ⟨h0, hle⟩ := rank_bound Phi sigma s hs hss (a k)
    exact douglas_pos t P _ ht htt h0 _ hle
  choose B hB1 hB2 using hk
  have hsA : s.comp ((∑ k ∈ Finset.range m, c k • rk (a k) (a k)).comp s) =
      ∑ k ∈ Finset.range m, c k • rk (s (a k)) (s (a k)) := by
    ext1 x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, map_sum, map_smul, rk_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← ContinuousLinearMap.adjoint_inner_left, hs]
  have hRHS : boundedOperator (Phi.val (operatorCoeff
      (s.comp ((∑ k ∈ Finset.range m, c k • rk (a k) (a k)).comp s)))) =
      ∑ k ∈ Finset.range m, c k •
        boundedOperator (Phi.val (operatorCoeff (rk (s (a k)) (s (a k))))) := by
    rw [hsA, coeff_sum]
    simp_rw [coeff_smul]
    rw [chan_sum Phi m c (fun k => operatorCoeff (rk (s (a k)) (s (a k)))) (fun k => tc_rk _ _)]
    apply bO_eq
    rw [coeff_sum]
    simp_rw [coeff_smul, coeff_bO (Phi.property.1 _ (tc_rk _ _))]
  refine ⟨∑ k ∈ Finset.range m, c k • B k, ?_, ?_⟩
  · ext1 x
    have h1 : ∀ k, (coefficientSupportProjection (Phi.val sigma.coefficients))
        (B k ((coefficientSupportProjection (Phi.val sigma.coefficients)) x)) = B k x :=
      fun k => congrArg (fun F : Hilbert J →L[ℂ] Hilbert J => F x) (hB1 k)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, map_sum, map_smul, h1]
  · rw [hRHS]
    ext1 x
    have h2 : ∀ k, t (B k (t x)) =
        boundedOperator (Phi.val (operatorCoeff (rk (s (a k)) (s (a k))))) x :=
      fun k => congrArg (fun F : Hilbert J →L[ℂ] Hilbert J => F x) (hB2 k)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, map_sum, map_smul, h2]


lemma unit_polar {I : Type} (u v : Hilbert I) :
    rk u v = ∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) •
      rk (u + Complex.I ^ k • v) (u + Complex.I ^ k • v) := by
  apply op_ext
  funext x y
  rw [coeff_sum, Matrix.sum_apply, coeff_rk]
  simp only [coeff_smul, Matrix.smul_apply, smul_eq_mul, coeff_rk, lp.coeFn_add, lp.coeFn_smul,
    Pi.add_apply, Pi.smul_apply]
  exact (polar4 (u x) (v x) (u y) (v y)).symm




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

lemma pair_summable {T : Type} (B : Hilbert T →L[ℂ] Hilbert T) {X : Matrix T T ℂ}
    (hX : IsTraceClass X) :
    Summable (fun i => operatorCoeff (B.comp (boundedOperator X)) i i) := by
  obtain ⟨e0⟩ := hX
  obtain ⟨e, he⟩ := balance e0
  rw [bO_nuc e]
  have hcoef : ∀ i, operatorCoeff (B.comp (nucOp e)) i i =
      ∑' n, star (e.right n i) * (B (e.left n)) i := by
    intro i
    rw [operatorCoeff_apply]
    have h := hasSum_coord ((nucOp_hasSum e (lp.single 2 i 1)).map B B.continuous) i
    show (B (nucOp e (lp.single 2 i 1))) i = _
    refine h.tsum_eq.symm.trans (tsum_congr (fun n => ?_))
    simp only [Function.comp, map_smul, inner_single_right', lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
  set g : ℕ → T → ℝ := fun n i => (‖e.right n i‖ ^ 2 + ‖(B (e.left n)) i‖ ^ 2) / 2 with hg
  have hg0 : ∀ n i, 0 ≤ g n i := fun n i => by rw [hg]; positivity
  have hrow : ∀ n, HasSum (fun i => g n i) ((‖e.right n‖ ^ 2 + ‖B (e.left n)‖ ^ 2) / 2) := by
    intro n
    exact ((hasSum_normSq (e.right n)).add (hasSum_normSq (B (e.left n)))).div_const 2
  have hcol : Summable (fun n => (‖e.right n‖ ^ 2 + ‖B (e.left n)‖ ^ 2) / 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((e0.summable.mul_left ((1 + ‖B‖ ^ 2) / 2)))
    have h1 : ‖e.right n‖ ^ 2 = ‖e0.left n‖ * ‖e0.right n‖ := (he n).2
    have h2 : ‖B (e.left n)‖ ^ 2 ≤ ‖B‖ ^ 2 * (‖e0.left n‖ * ‖e0.right n‖) := by
      rw [← (he n).1, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2
    rw [h1]; nlinarith
  have hu : Summable (fun p : ℕ × T => g p.1 p.2) :=
    (summable_prod_of_nonneg (fun p => hg0 p.1 p.2)).2
      ⟨fun n => (hrow n).summable, by simpa only [(hrow _).tsum_eq] using hcol⟩
  have hu' : Summable (fun p : T × ℕ => g p.2 p.1) :=
    ((Equiv.prodComm T ℕ).summable_iff (f := fun p : ℕ × T => g p.1 p.2)).mpr hu
  have hi : Summable (fun i => ∑' n, g n i) := hu'.prod
  refine Summable.of_norm_bounded hi (fun i => ?_)
  rw [hcoef]
  have hsn : Summable (fun n => g n i) := hu'.prod_factor i
  have hb : ∀ n, ‖star (e.right n i) * (B (e.left n)) i‖ ≤ g n i := by
    intro n
    rw [norm_mul, norm_star, hg]
    nlinarith [sq_nonneg (‖e.right n i‖ - ‖(B (e.left n)) i‖)]
  have hs : Summable (fun n => ‖star (e.right n i) * (B (e.left n)) i‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hsn
  calc ‖∑' n, star (e.right n i) * (B (e.left n)) i‖
      ≤ ∑' n, ‖star (e.right n i) * (B (e.left n)) i‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, g n i := Summable.tsum_le_tsum hb hs hsn

lemma pair_add {T : Type} (B : Hilbert T →L[ℂ] Hilbert T) {X Y : Matrix T T ℂ}
    (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    boundedTracePair (X + Y) B = boundedTracePair X B + boundedTracePair Y B := by
  unfold boundedTracePair
  rw [bO_add hX hY, ContinuousLinearMap.comp_add, coeff_add]
  exact (pair_summable B hX).tsum_add (pair_summable B hY)

lemma pair_smul {T : Type} (B : Hilbert T →L[ℂ] Hilbert T) (c : ℂ) {X : Matrix T T ℂ}
    (hX : IsTraceClass X) :
    boundedTracePair (c • X) B = c • boundedTracePair X B := by
  unfold boundedTracePair
  rw [bO_smul c hX, ContinuousLinearMap.comp_smul, coeff_smul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact tsum_mul_left



/-! ## s3: uniqueness of the supported dual (U1) and D(I) = I (U2 part) -/

open ContinuousLinearMap in
lemma mem_K {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (t P : E →L[ℂ] E) (ht : adjoint t = t) (htt : t * t = P) (x : E) :
    t x ∈ (LinearMap.range P.toLinearMap).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro u hu
  rw [Submodule.mem_orthogonal'] at hu
  have h1 : inner ℂ u (P u) = 0 := hu (P u) ⟨u, rfl⟩
  have h2 : t u = 0 := by
    have : inner ℂ (t u) (t u) = 0 := by
      rw [← adjoint_inner_right, ht, ← h1, ← htt]; rfl
    exact inner_self_eq_zero.mp this
  rw [← adjoint_inner_left, ht, h2, inner_zero_left]


/-! ## s4 U5: a PSD matrix with summable diagonal is trace class -/









/-! ## s4: positivity of trace pairings -/

/-! ## s4 U3: complete positivity pieces -/






lemma isDensity_rk {T : Type} (ξ : Hilbert T) (hξ : ‖ξ‖ = 1) :
    IsDensity (operatorCoeff (rk ξ ξ)) := by
  let w : ℕ → Hilbert T := fun m => if m = 0 then ξ else 0
  have hw0 : ∀ m, m ≠ 0 → ‖w m‖ ^ 2 = 0 := fun m hm => by simp [w, hm]
  have hw : HasSum (fun m => ‖w m‖ ^ 2) 1 := by
    have := hasSum_single (f := fun m => ‖w m‖ ^ 2) 0 hw0
    simpa [w, hξ] using this
  have h := isDensity_mat w hw.summable (by rw [hw.tsum_eq]; norm_num)
  rw [hw.tsum_eq, inv_one, Complex.ofReal_one, one_smul] at h
  convert h using 1
  funext p q
  rw [coeff_rk, Mat, tsum_eq_single 0 (fun m hm => by simp [w, hm])]
  simp [w]




lemma rk_smul_smul {T : Type} (c : ℂ) (u v : Hilbert T) :
    rk (c • u) (c • v) = (c * star c) • rk u v := by
  ext1 x
  simp only [rk_apply, ContinuousLinearMap.smul_apply, inner_smul_left, smul_smul]
  congr 1
  simp only [Complex.star_def]
  ring


/-! ## s5: pairing through a rank-one expansion over any index (U3e core) -/

lemma gen_summable {T K : Type} (u v : K → Hilbert T) (h : Summable (fun k => ‖u k‖ * ‖v k‖)) :
    Summable (fun k => rk (u k) (v k)) :=
  Summable.of_norm_bounded h (fun k => norm_rk _ _)

lemma bO_gen {T K : Type} (u v : K → Hilbert T) (h : Summable (fun k => ‖u k‖ * ‖v k‖))
    {X : Matrix T T ℂ} (hX : ∀ i j, HasSum (fun k => u k i * star (v k j)) (X i j)) :
    boundedOperator X = ∑' k, rk (u k) (v k) := by
  apply bO_eq
  funext i j
  rw [operatorCoeff_apply]
  have h1 := (gen_summable u v h).hasSum.map
    (ContinuousLinearMap.apply ℂ (Hilbert T) (lp.single 2 j (1:ℂ))) (ContinuousLinearMap.continuous _)
  have h2 := hasSum_coord h1 i
  refine h2.unique ?_
  convert hX i j using 1
  funext k
  simp [Function.comp, rk_apply, inner_single_right', mul_comm]

lemma pair_gen {T K : Type} (B : Hilbert T →L[ℂ] Hilbert T) (u v : K → Hilbert T)
    (h : Summable (fun k => ‖u k‖ * ‖v k‖))
    {X : Matrix T T ℂ} (hX : ∀ i j, HasSum (fun k => u k i * star (v k j)) (X i j)) :
    HasSum (fun k => inner ℂ (v k) (B (u k))) (boundedTracePair X B) := by
  unfold boundedTracePair
  rw [bO_gen u v h hX]
  have hcoef : ∀ i, operatorCoeff (B.comp (∑' k, rk (u k) (v k))) i i =
      ∑' k, star (v k i) * (B (u k)) i := by
    intro i
    rw [operatorCoeff_apply]
    have h1 := (gen_summable u v h).hasSum.map
      (ContinuousLinearMap.apply ℂ (Hilbert T) (lp.single 2 i (1:ℂ)))
      (ContinuousLinearMap.continuous _)
    have h2 := hasSum_coord (h1.map B B.continuous) i
    show (B ((∑' k, rk (u k) (v k)) (lp.single 2 i 1))) i = _
    refine h2.tsum_eq.symm.trans (tsum_congr (fun k => ?_))
    simp [Function.comp, rk_apply, inner_single_right']
  simp_rw [hcoef]
  have hH : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have hu : Summable (Function.uncurry (fun (i : T) (k : K) => ‖v k i‖ * ‖(B (u k)) i‖)) := by
    refine summable_uncurry_of_swap (fun (i : T) (k : K) => ‖v k i‖ * ‖(B (u k)) i‖)
      (fun i k => by positivity) (fun k => lp.summable_mul hH (v k) (B (u k))) ?_
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg (fun i => by positivity))
      (fun k => ?_) (h.mul_left ‖B‖)
    calc ∑' i, ‖v k i‖ * ‖(B (u k)) i‖ ≤ ‖v k‖ * ‖B (u k)‖ := lp.tsum_mul_le_mul_norm' hH _ _
      _ ≤ ‖v k‖ * (‖B‖ * ‖u k‖) := mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
      _ = ‖B‖ * (‖u k‖ * ‖v k‖) := by ring
  rw [tsum_swap_of (fun (i : T) (k : K) => star (v k i) * (B (u k)) i)
    (fun (i : T) (k : K) => ‖v k i‖ * ‖(B (u k)) i‖)
    (fun i k => le_of_eq (by rw [norm_mul, norm_star])) hu]
  have hS : Summable (fun k => inner ℂ (v k) (B (u k))) := by
    refine Summable.of_norm_bounded (h.mul_left ‖B‖) (fun k => ?_)
    calc ‖inner ℂ (v k) (B (u k))‖ ≤ ‖v k‖ * ‖B (u k)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v k‖ * (‖B‖ * ‖u k‖) := mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
      _ = ‖B‖ * (‖u k‖ * ‖v k‖) := by ring
  convert hS.hasSum using 1
  exact tsum_congr (fun k => (inner_eq_tsum' _ _).symm)






/-! ## s5: U3b, positivity of the supported dual on rank-one families -/

lemma rk_conj {T : Type} {s : Hilbert T →L[ℂ] Hilbert T} (hs : ContinuousLinearMap.adjoint s = s)
    (u v : Hilbert T) : s.comp ((rk u v).comp s) = rk (s u) (s v) := by
  ext1 x
  simp only [ContinuousLinearMap.comp_apply, rk_apply, map_smul]
  rw [sa_swap hs]

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- Existence and defining equations of the supported dual on a rank-one operator. -/
lemma dual_rk {I J : Type} (Phi : Channel I J) (sigma : State I) (u v : Hilbert I) :
    (coefficientSupportProjection (Phi.val sigma.coefficients)).comp
        ((petzSupportedDual Phi.val sigma.coefficients (rk u v)).comp
          (coefficientSupportProjection (Phi.val sigma.coefficients))) =
      petzSupportedDual Phi.val sigma.coefficients (rk u v) ∧
    (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients))).comp
        ((petzSupportedDual Phi.val sigma.coefficients (rk u v)).comp
          (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)))) =
      boundedOperator (Phi.val (operatorCoeff
        (rk (positiveSquareRoot (boundedOperator sigma.coefficients) u)
          (positiveSquareRoot (boundedOperator sigma.coefficients) v)))) := by
  obtain ⟨hs, _, _⟩ := sqrt_state sigma
  have hex := good_sum Phi sigma 4 (fun k => Complex.I ^ k / 4) (fun k => u + Complex.I ^ k • v)
  beta_reduce at hex
  rw [← unit_polar u v] at hex
  unfold petzSupportedDual
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact ⟨h1, h2.trans (by rw [rk_conj hs])⟩








/-! ## s6: U4 normality of the Petz dual -/
































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














/-- The image state of a channel. -/
def phiS {J : Type} (Phi : Channel I J) (rho : State I) : State J :=
  ⟨Phi.val rho.coefficients, chan_density Phi.val Phi.property _ rho.density⟩




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
noncomputable local instance (priority := 1100) scC_acm_4 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_mod_4 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Module ℂ (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scC_top_4 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : TopologicalSpace (E →L[ℂ] F) := inferInstance
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

/-- t*t is the norm-convergent sum of rank-one operators rankOne (t b_k) (t b_k)
when t is self-adjoint and Hilbert-Schmidt in the complete family b. -/
theorem sq_hasSum_rankOne {β : Type} (b : β → E) (hb : ∀ x, HasSum (fun k => ⟪b k, x⟫_ℂ • b k) x)
    (t : E →L[ℂ] E) (ht : ContinuousLinearMap.adjoint t = t)
    (hHS : Summable (fun k => ‖t (b k)‖ ^ 2)) :
    HasSum (fun k => InnerProductSpace.rankOne ℂ (t (b k)) (t (b k))) (t * t) := by
  have hsn : Summable (fun k => InnerProductSpace.rankOne ℂ (t (b k)) (t (b k))) := by
    refine Summable.of_norm_bounded hHS (fun k => ?_)
    calc _ ≤ ‖t (b k)‖ * ‖t (b k)‖ := norm_rankOne_le _ _
      _ = ‖t (b k)‖ ^ 2 := by ring
  obtain ⟨S, hS⟩ := hsn
  have hSeq : S = t * t := by
    ext x
    have h1 := hS.mapL (ContinuousLinearMap.apply ℂ E x)
    simp only [ContinuousLinearMap.apply_apply, InnerProductSpace.rankOne_apply] at h1
    have h2 := (hb (t x)).mapL t
    simp only [map_smul] at h2
    have h3 : (fun k => ⟪b k, t x⟫_ℂ • t (b k)) = fun k => ⟪t (b k), x⟫_ℂ • t (b k) := by
      funext k
      congr 1
      rw [← ContinuousLinearMap.adjoint_inner_left t x (b k), ht]
    rw [h3] at h2
    rw [ContinuousLinearMap.mul_apply]
    exact h1.unique h2
  rw [← hSeq]
  exact hS

theorem sq_compact {β : Type} (b : β → E) (hb : ∀ x, HasSum (fun k => ⟪b k, x⟫_ℂ • b k) x)
    (t : E →L[ℂ] E) (ht : ContinuousLinearMap.adjoint t = t)
    (hHS : Summable (fun k => ‖t (b k)‖ ^ 2)) : IsCompactOperator (t * t) := by
  classical
  have h := sq_hasSum_rankOne b hb t ht hHS
  refine isCompactOperator_of_tendsto h (Filter.Eventually.of_forall (fun F => ?_))
  induction F using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | insert k F hk ih =>
    rw [Finset.sum_insert hk]
    exact (rankOne_compact _ _).add ih

end Compact

section Eigen

/-- Hilbert-Schmidt norm is basis independent: Sum ‖t b_k‖^2 = Sum ‖t* e_i‖^2. -/
theorem hs_swap {β : Type} (e : HilbertBasis ι ℂ E) (b : HilbertBasis β ℂ E) (t : E →L[ℂ] E)
    {S : ℝ} (h : HasSum (fun k => ‖t (b k)‖ ^ 2) S) :
    HasSum (fun i => ‖(ContinuousLinearMap.adjoint t) (e i)‖ ^ 2) S := by
  set f : β × ι → ℝ := fun p => ‖⟪e p.2, t (b p.1)⟫_ℂ‖ ^ 2 with hfdef
  have hf0 : ∀ p, 0 ≤ f p := fun p => sq_nonneg _
  have hF : HasSum f S := by
    have := hasSum_prod_of_fibers_nonneg (f := f) hf0 (g := fun k => ‖t (b k)‖ ^ 2)
      (fun k => hb_norm_sq e (t (b k))) h.summable
    rwa [h.tsum_eq] at this
  have hF' : HasSum (fun q : ι × β => f (q.2, q.1)) S :=
    ((Equiv.prodComm ι β).hasSum_iff (f := f)).mpr hF
  refine hF'.prod_fiberwise (fun i => ?_)
  have hb := hb_norm_sq b ((ContinuousLinearMap.adjoint t) (e i))
  convert hb using 2 with k
  simp only [hfdef]
  rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, Complex.norm_conj]

/-- Eigen data of t*t for t self-adjoint Hilbert-Schmidt: a Hilbert basis of eigenvectors with
nonnegative eigenvalues summing to the HS norm. -/
theorem eigen_data {β : Type} (b : HilbertBasis β ℂ E) (t : E →L[ℂ] E)
    (ht : ContinuousLinearMap.adjoint t = t) {S : ℝ} (hHS : HasSum (fun k => ‖t (b k)‖ ^ 2) S) :
    ∃ (ι : Type) (e : HilbertBasis ι ℂ E) (r : ι → ℝ), (∀ i, 0 ≤ r i) ∧ HasSum r S ∧
      (∀ i, (t * t) (e i) = (r i : ℂ) • e i) := by
  have hbx : ∀ x, HasSum (fun k => ⟪b k, x⟫_ℂ • b k) x := by
    intro x
    have := b.hasSum_repr x
    simpa [HilbertBasis.repr_apply_apply] using this
  have hc : IsCompactOperator (t * t) := sq_compact b hbx t ht hHS.summable
  have hsa : IsSelfAdjoint (t * t) := by
    have h1 : IsSelfAdjoint (star t * t) := IsSelfAdjoint.star_mul_self t
    have h2 : star t = t := ht
    rwa [h2] at h1
  have hsym : ((t * t : E →L[ℂ] E) : E →ₗ[ℂ] E).IsSymmetric := hsa.isSymmetric
  obtain ⟨ι, e, lam, hlam⟩ := exists_eigenbasis (t * t) hc hsym
  have hr : ∀ i, lam i = ‖t (e i)‖ ^ 2 := by
    intro i
    have h1 : ⟪e i, (t * t) (e i)⟫_ℂ = (lam i : ℂ) := by
      rw [hlam i, inner_smul_right, inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]
      simp
    have h2 : ⟪e i, (t * t) (e i)⟫_ℂ = ((‖t (e i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left, ht,
        inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have := h1.symm.trans h2
    exact_mod_cast this
  refine ⟨ι, e, lam, fun i => by rw [hr i]; exact sq_nonneg _, ?_, hlam⟩
  have := hs_swap e b t hHS
  rw [ht] at this
  convert this using 1
  funext i
  exact hr i

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

/-- A bounded sesquilinear form is represented by a bounded operator. -/
theorem exists_op_of_form (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
    ∃ D : E →L[ℂ] E, ∀ x y, ⟪x, D y⟫_ℂ = f x y := by
  let B0 : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) f H1
    (fun c x y => by rw [H2]; rfl) H3 (fun c x y => by rw [H4]; rfl)
  let B : E →L⋆[ℂ] E →L[ℂ] ℂ := B0.mkContinuous₂ C hC
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin B),
    fun x y => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

omit [CompleteSpace E] in
theorem polar_form (x y : E) :
    4 * f x y = f (y + x) (y + x) - f (y + (-1 : ℂ) • x) (y + (-1 : ℂ) • x)
      + Complex.I * f (y + Complex.I • x) (y + Complex.I • x)
      - Complex.I * f (y + (-Complex.I) • x) (y + (-Complex.I) • x) := by
  simp only [H1, H3, H2, H4, map_neg, map_one, Complex.conj_I]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (2 * f x y - 2 * f y x) * hI

omit [CompleteSpace E] in
theorem form_zero_left (y : E) : f 0 y = 0 := by
  have h := H2 0 0 y
  rw [zero_smul, map_zero, zero_mul] at h
  exact h

omit [CompleteSpace E] in
theorem form_zero_right (x : E) : f x 0 = 0 := by
  have h := H4 0 x 0
  rw [zero_smul, zero_mul] at h
  exact h

omit [CompleteSpace E] in
theorem polar_bound (K : ℝ) (hK : ∀ z, ‖f z z‖ ≤ K * ‖z‖ ^ 2) (x y : E) :
    ‖f x y‖ ≤ K * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hp := polar_form f H1 H2 H3 H4 x y
  have hn : ∀ c : ℂ, ‖c‖ = 1 → ‖y + c • x‖ ^ 2 + ‖y + (-c) • x‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    intro c hc
    rw [neg_smul, ← sub_eq_add_neg, @norm_add_sq ℂ, @norm_sub_sq ℂ, norm_smul, hc, one_mul]
    ring
  have h4 : ‖(4 : ℂ) * f x y‖ ≤ K * ‖y + x‖ ^ 2 + K * ‖y + (-1 : ℂ) • x‖ ^ 2
      + K * ‖y + Complex.I • x‖ ^ 2 + K * ‖y + (-Complex.I) • x‖ ^ 2 := by
    rw [hp]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (hK _) (hK _))) ?_)) ?_
    · rw [norm_mul, Complex.norm_I, one_mul]; exact hK _
    · rw [norm_mul, Complex.norm_I, one_mul]; exact hK _
  have e1 := hn 1 (by simp)
  have e2 := hn Complex.I Complex.norm_I
  rw [one_smul] at e1
  rw [norm_mul] at h4
  have h44 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h44] at h4
  have hs : K * ‖y + x‖ ^ 2 + K * ‖y + (-1 : ℂ) • x‖ ^ 2 + K * ‖y + Complex.I • x‖ ^ 2
      + K * ‖y + (-Complex.I) • x‖ ^ 2 = 4 * (K * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
    linear_combination K * e1 + K * e2
  linarith

omit [CompleteSpace E] in
theorem form_bound (K : ℝ) (hK : ∀ z, ‖f z z‖ ≤ K * ‖z‖ ^ 2) (x y : E) :
    ‖f x y‖ ≤ 2 * K * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; rw [form_zero_left f H1 H2 H3 H4]; simp
  rcases eq_or_ne y 0 with hy | hy
  · subst hy; rw [form_zero_right f H1 H2 H3 H4]; simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set a : ℝ := Real.sqrt (‖y‖ / ‖x‖) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (div_pos hyn hxn)
  have ha2 : a ^ 2 = ‖y‖ / ‖x‖ := Real.sq_sqrt (div_pos hyn hxn).le
  have hfe : f ((a : ℂ) • x) (((a⁻¹ : ℝ) : ℂ) • y) = f x y := by
    rw [H2, H4, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ha0.ne',
      Complex.ofReal_one, one_mul]
  have hb := polar_bound f H1 H2 H3 H4 K hK ((a : ℂ) • x) (((a⁻¹ : ℝ) : ℂ) • y)
  rw [hfe, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos ha0, abs_of_pos (inv_pos.mpr ha0)] at hb
  have h1 : (a * ‖x‖) ^ 2 = ‖x‖ * ‖y‖ := by
    rw [mul_pow, ha2]; field_simp
  have h2 : (a⁻¹ * ‖y‖) ^ 2 = ‖x‖ * ‖y‖ := by
    rw [mul_pow, inv_pow, ha2]; field_simp
  rw [h1, h2] at hb
  linarith

end Forms

end P45C4


end

end C4aPart

/-! ## C4 bridge: eigen data of a State and the trace pairing in eigen coordinates (s12) -/
section C4Bridge

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace P45C4B
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
noncomputable local instance (priority := 1100) scH_us_5 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_am_5 (X Y : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_azc_5 (X Y : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
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

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open P45Petz P45C4
open scoped InnerProductSpace

/-- The standard Hilbert basis of `Hilbert T`. -/
def stdB (T : Type) : HilbertBasis T ℂ (Hilbert T) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (Hilbert T))

lemma stdB_apply {T : Type} (k : T) : stdB T k = bvec k := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

/-- A state has an eigen Hilbert basis with nonnegative eigenvalues summing to one. -/
theorem state_eigen {T : Type} (rho : State T) :
    ∃ (ι : Type) (e : HilbertBasis ι ℂ (Hilbert T)) (r : ι → ℝ), (∀ i, 0 ≤ r i) ∧ HasSum r 1 ∧
      (∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i) := by
  obtain ⟨ht, htt, hHS⟩ := sqrt_state rho
  set t := QAlgorithms.Papers.Independent.Next46.P31.positiveSquareRoot
    (boundedOperator rho.coefficients) with htdef
  have hHS' : HasSum (fun k => ‖t (stdB T k)‖ ^ 2) (1 : ℝ) := by
    simp_rw [stdB_apply]; exact hHS
  obtain ⟨ι, e, r, hr0, hr1, hev⟩ := eigen_data (stdB T) t ht hHS'
  exact ⟨ι, e, r, hr0, hr1, fun i => by rw [← htt]; exact hev i⟩

/-- The trace pairing in an eigenbasis: Tr(rho W) = Sum r_i <e_i, W e_i>. -/
theorem pair_eigen {T ι : Type} (rho : State T) (e : HilbertBasis ι ℂ (Hilbert T)) (r : ι → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (W : Hilbert T →L[ℂ] Hilbert T) :
    HasSum (fun i => (r i : ℂ) * ⟪e i, W (e i)⟫_ℂ) (boundedTracePair rho.coefficients W) := by
  set u : ι → Hilbert T := fun k => ((Real.sqrt (r k) : ℝ) : ℂ) • e k with hu
  have hnu : ∀ k, ‖u k‖ = Real.sqrt (r k) := by
    intro k
    rw [hu, norm_smul, e.orthonormal.1 k, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq : ∀ k, Real.sqrt (r k) * Real.sqrt (r k) = r k := fun k => Real.mul_self_sqrt (hr0 k)
  have hsum : Summable (fun k => ‖u k‖ * ‖u k‖) := by
    simp_rw [hnu, hsq]; exact hr1
  have hX : ∀ i j, HasSum (fun k => u k i * star (u k j)) (rho.coefficients i j) := by
    intro i j
    have h1 := hasSum_coord (eigen_expand e r hev (bvec j)) i
    have h2 : (boundedOperator rho.coefficients (bvec j)) i = rho.coefficients i j := by
      have := congrFun (congrFun (coeff_bO rho.density.1) i) j
      rw [← this, operatorCoeff_apply]; rfl
    rw [h2] at h1
    convert h1 using 1
    funext k
    have h3 : ⟪e k, bvec j⟫_ℂ = star (e k j) := inner_single_right' (e k) j
    simp only [hu, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, h3, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    have h4 : ((Real.sqrt (r k) : ℝ) : ℂ) * ((Real.sqrt (r k) : ℝ) : ℂ) = (r k : ℂ) := by
      rw [← Complex.ofReal_mul, hsq]
    linear_combination (e k i * (starRingEnd ℂ) (e k j)) * h4
  have h := pair_gen W u u hsum hX
  convert h using 1
  funext k
  simp only [hu, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  have h4 : ((Real.sqrt (r k) : ℝ) : ℂ) * ((Real.sqrt (r k) : ℝ) : ℂ) = (r k : ℂ) := by
    rw [← Complex.ofReal_mul, hsq]
  linear_combination (-⟪e k, W (e k)⟫_ℂ) * h4


/-- |Tr(rho W)| ≤ ‖W‖ for a state. -/
theorem pair_state_bound {T : Type} (rho : State T) (W : Hilbert T →L[ℂ] Hilbert T) :
    ‖boundedTracePair rho.coefficients W‖ ≤ ‖W‖ := by
  obtain ⟨ι, e, r, hr0, hr1, hev⟩ := state_eigen rho
  have h := pair_eigen rho e r hr0 hr1.summable hev W
  have hg : HasSum (fun i => r i * ‖W‖) (1 * ‖W‖) := hr1.mul_right _
  rw [one_mul] at hg
  refine h.norm_le_of_bounded hg (fun i => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 i)]
  refine mul_le_mul_of_nonneg_left ?_ (hr0 i)
  calc ‖⟪e i, W (e i)⟫_ℂ‖ ≤ ‖e i‖ * ‖W (e i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖e i‖ * (‖W‖ * ‖e i‖) := mul_le_mul_of_nonneg_left (W.le_opNorm _) (norm_nonneg _)
    _ = ‖W‖ := by rw [e.orthonormal.1 i]; ring

section Dual

variable {I J : Type}

/-- G(R) = Tr(Phi(R) W). -/
def dG (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (R : Hilbert I →L[ℂ] Hilbert I) : ℂ :=
  boundedTracePair (Phi.val (operatorCoeff R)) W

lemma dG_lin (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (a : ℂ)
    (R1 R2 : Hilbert I →L[ℂ] Hilbert I)
    (h1 : IsTraceClass (operatorCoeff R1)) (h2 : IsTraceClass (operatorCoeff R2)) :
    dG Phi W (a • R1 + R2) = a * dG Phi W R1 + dG Phi W R2 := by
  unfold dG
  rw [coeff_add, coeff_smul, Phi.property.2.1 _ _ (tc_smul a h1) h2, Phi.property.2.2.1 a _ h1,
    pair_add W (tc_smul a (Phi.property.1 _ h1)) (Phi.property.1 _ h2),
    pair_smul W a (Phi.property.1 _ h1), smul_eq_mul]

lemma tc_zero_op : IsTraceClass (operatorCoeff (0 : Hilbert I →L[ℂ] Hilbert I)) := by
  have h : operatorCoeff (0 : Hilbert I →L[ℂ] Hilbert I) = 0 := by
    funext i j; simp [operatorCoeff]
  rw [h]; exact tc_zero

lemma dG_zero (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) : dG Phi W 0 = 0 := by
  have h := dG_lin Phi W 1 0 0 tc_zero_op tc_zero_op
  simp only [smul_zero, add_zero, one_mul] at h
  linear_combination -h

lemma dG_smul (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (c : ℂ)
    (R : Hilbert I →L[ℂ] Hilbert I) (h : IsTraceClass (operatorCoeff R)) :
    dG Phi W (c • R) = c * dG Phi W R := by
  have := dG_lin Phi W c R 0 h tc_zero_op
  rwa [add_zero, dG_zero, add_zero] at this

lemma dG_add (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J)
    (R1 R2 : Hilbert I →L[ℂ] Hilbert I)
    (h1 : IsTraceClass (operatorCoeff R1)) (h2 : IsTraceClass (operatorCoeff R2)) :
    dG Phi W (R1 + R2) = dG Phi W R1 + dG Phi W R2 := by
  have := dG_lin Phi W 1 R1 R2 h1 h2
  rwa [one_smul, one_mul] at this

lemma c4rk_add_l (u1 u2 v : Hilbert I) : rk (u1 + u2) v = rk u1 v + rk u2 v := by
  ext1 x; simp [rk_apply, smul_add]

lemma c4rk_add_r (u v1 v2 : Hilbert I) : rk u (v1 + v2) = rk u v1 + rk u v2 := by
  ext1 x; simp [rk_apply, inner_add_left, add_smul]

lemma c4rk_smul_l (c : ℂ) (u v : Hilbert I) : rk (c • u) v = c • rk u v := by
  ext1 x; simp only [rk_apply, ContinuousLinearMap.smul_apply]; rw [smul_comm]

lemma c4rk_smul_r (c : ℂ) (u v : Hilbert I) : rk u (c • v) = (starRingEnd ℂ c) • rk u v := by
  ext1 x; simp only [rk_apply, ContinuousLinearMap.smul_apply, inner_smul_left, smul_smul]

/-- dF x y = Tr(Phi(|y><x|) W), the matrix element <x, Phi*(W) y>. -/
def dF (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (x y : Hilbert I) : ℂ :=
  dG Phi W (rk y x)

lemma dF_H1 (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (x1 x2 y : Hilbert I) :
    dF Phi W (x1 + x2) y = dF Phi W x1 y + dF Phi W x2 y := by
  unfold dF; rw [c4rk_add_r, dG_add _ _ _ _ (tc_rk _ _) (tc_rk _ _)]

lemma dF_H2 (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (c : ℂ) (x y : Hilbert I) :
    dF Phi W (c • x) y = (starRingEnd ℂ) c * dF Phi W x y := by
  unfold dF; rw [c4rk_smul_r, dG_smul _ _ _ _ (tc_rk _ _)]

lemma dF_H3 (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (x y1 y2 : Hilbert I) :
    dF Phi W x (y1 + y2) = dF Phi W x y1 + dF Phi W x y2 := by
  unfold dF; rw [c4rk_add_l, dG_add _ _ _ _ (tc_rk _ _) (tc_rk _ _)]

lemma dF_H4 (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (c : ℂ) (x y : Hilbert I) :
    dF Phi W x (c • y) = c * dF Phi W x y := by
  unfold dF; rw [c4rk_smul_l, dG_smul _ _ _ _ (tc_rk _ _)]

lemma dF_diag (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (z : Hilbert I) :
    ‖dF Phi W z z‖ ≤ ‖W‖ * ‖z‖ ^ 2 := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    have h0 : rk (0 : Hilbert I) 0 = 0 := by ext1 v; simp [rk_apply]
    unfold dF; rw [h0, dG_zero]; simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set zh : Hilbert I := ((‖z‖⁻¹ : ℝ) : ℂ) • z with hzh
  have hzh1 : ‖zh‖ = 1 := by
    rw [hzh, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  have hz' : z = ((‖z‖ : ℝ) : ℂ) • zh := by
    rw [hzh, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hrk : rk z z = (((‖z‖ ^ 2 : ℝ)) : ℂ) • rk zh zh := by
    conv_lhs => rw [hz']
    rw [rk_smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    ring
  have hd : IsDensity (Phi.val (operatorCoeff (rk zh zh))) :=
    chan_density Phi.val Phi.property _ (isDensity_rk zh hzh1)
  have hb := pair_state_bound ⟨_, hd⟩ W
  unfold dF
  rw [hrk, dG_smul _ _ _ _ (tc_rk _ _), norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  unfold dG
  nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg ‖z‖)]

theorem dual_exists (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) :
    ∃ D : Hilbert I →L[ℂ] Hilbert I, ∀ x y, ⟪x, D y⟫_ℂ = dF Phi W x y :=
  exists_op_of_form (dF Phi W) (dF_H1 Phi W) (dF_H2 Phi W) (dF_H3 Phi W) (dF_H4 Phi W) _
    (fun x y => by
      have := form_bound (dF Phi W) (dF_H1 Phi W) (dF_H2 Phi W) (dF_H3 Phi W) (dF_H4 Phi W)
        ‖W‖ (dF_diag Phi W) x y
      exact this)

lemma coeff_rk_bvec (i j : I) : operatorCoeff (rk (bvec j) (bvec i)) = Matrix.single j i (1 : ℂ) := by
  funext a b
  rw [coeff_rk]
  simp only [bvec, lp.single_apply, Matrix.single_apply, Pi.single_apply]
  by_cases ha : a = j <;> by_cases hb : b = i <;> simp [ha, hb] <;> intro h <;> simp_all

/-- The official channel dual: <x, Phi*(W) y> = Tr(Phi(|y><x|) W). -/
theorem channelDual_inner (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (x y : Hilbert I) :
    ⟪x, channelDual Phi.val W y⟫_ℂ = dF Phi W x y := by
  obtain ⟨D, hD⟩ := dual_exists Phi W
  have hc : channelDual Phi.val W = D := by
    unfold channelDual
    apply bO_eq
    funext i j
    rw [operatorCoeff_apply, coord_eq_inner]
    change ⟪bvec i, D (bvec j)⟫_ℂ = _
    rw [hD]
    unfold dF dG
    rw [coeff_rk_bvec]
  rw [hc, hD]

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
noncomputable local instance (priority := 1100) scH_ns_6 (X : Type) : NormedSpace ℂ (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_top_6 (X : Type) : TopologicalSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_am_6 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_6 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_6 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_6 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_am_6 (X Y : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
noncomputable local instance (priority := 1100) scHC_azc_6 (X Y : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
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

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity IsTraceClassChannel)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)
open P45Petz P45N0


section GenN1b
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]








end GenN1b







/-- Hilbert-Schmidt trace cyclicity: Tr(Y X) = Tr(X Y) when X and Y have square-summable columns. -/
lemma tr_cyc {T : Type} (X Y : Hilbert T →L[ℂ] Hilbert T)
    (hX : Summable (fun i => ‖X (bvec i)‖ ^ 2)) (hY : Summable (fun k => ‖Y (bvec k)‖ ^ 2)) :
    ∑' i, inner ℂ (bvec i) (Y (X (bvec i))) = ∑' k, inner ℂ (bvec k) (X (Y (bvec k))) := by
  have hexp : ∀ (A : Hilbert T →L[ℂ] Hilbert T) (v : Hilbert T) (i : T),
      HasSum (fun k => v k * (A (bvec k)) i) ((A v) i) := by
    intro A v i
    have h2 := (hasSum_basis v).mapL A
    have h3 := hasSum_coord h2 i
    simpa [map_smul, smul_eq_mul, bvec] using h3
  have hL : ∀ i, inner ℂ (bvec i) (Y (X (bvec i))) = ∑' k, (X (bvec i)) k * (Y (bvec k)) i := by
    intro i; rw [inner_bvec_left]; exact (hexp Y (X (bvec i)) i).tsum_eq.symm
  have hR : ∀ k, inner ℂ (bvec k) (X (Y (bvec k))) = ∑' i, (Y (bvec k)) i * (X (bvec i)) k := by
    intro k; rw [inner_bvec_left]; exact (hexp X (Y (bvec k)) k).tsum_eq.symm
  simp_rw [hL, hR]
  set g1 : T → T → ℝ := fun i k => ‖(X (bvec i)) k‖ ^ 2 with hg1
  set g2 : T → T → ℝ := fun i k => ‖(Y (bvec k)) i‖ ^ 2 with hg2
  have hu1 : Summable (Function.uncurry g1) := by
    refine (summable_prod_of_nonneg (fun p => sq_nonneg _)).2 ⟨fun i => ?_, ?_⟩
    · exact (hasSum_normSq (X (bvec i))).summable
    · refine hX.congr (fun i => ?_)
      exact (hasSum_normSq (X (bvec i))).tsum_eq.symm
  have hu2 : Summable (Function.uncurry g2) := by
    refine summable_uncurry_of_swap g2 (fun _ _ => sq_nonneg _)
      (fun k => (hasSum_normSq (Y (bvec k))).summable) ?_
    refine hY.congr (fun k => ?_)
    exact (hasSum_normSq (Y (bvec k))).tsum_eq.symm
  have hu : Summable (Function.uncurry (fun i k => g1 i k + g2 i k)) := hu1.add hu2
  rw [tsum_swap_of (fun i k => (X (bvec i)) k * (Y (bvec k)) i) (fun i k => g1 i k + g2 i k)
    (fun i k => ?_) hu]
  · refine tsum_congr (fun k => tsum_congr (fun i => ?_))
    ring
  · simp only [hg1, hg2, norm_mul]
    nlinarith [norm_nonneg ((X (bvec i)) k), norm_nonneg ((Y (bvec k)) i),
      sq_nonneg (‖(X (bvec i)) k‖ - ‖(Y (bvec k)) i‖)]

lemma hs_col {T : Type} (B t : Hilbert T →L[ℂ] Hilbert T)
    (ht : Summable (fun k => ‖t (bvec k)‖ ^ 2)) :
    Summable (fun k => ‖(B.comp t) (bvec k)‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_) (ht.mul_left (‖B‖ ^ 2))
  rw [ContinuousLinearMap.comp_apply, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2

open P45C4B in
/-- N1c: a Petz-recovered state is the sigma-sandwich of the dual of its Douglas solution. -/
theorem n1c {I J : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho sigma : State I)
    (hP : rho.coefficients = petzRecovery Phi.val sigma.coefficients (Phi.val rho.coefficients))
    (B : Hilbert J →L[ℂ] Hilbert J) (c : ℝ) (hc : 0 < c)
    (hB : (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients))).comp
        (B.comp (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)))) =
      (c : ℂ) • boundedOperator (Phi.val rho.coefficients)) :
    (positiveSquareRoot (boundedOperator sigma.coefficients)).comp
        ((channelDual Phi.val B).comp (positiveSquareRoot (boundedOperator sigma.coefficients))) =
      (c : ℂ) • boundedOperator rho.coefficients := by
  set P := boundedOperator (Phi.val sigma.coefficients) with hPdef
  set t := positiveSquareRoot P with htdef
  set s := positiveSquareRoot (boundedOperator sigma.coefficients) with hsdef
  set S := coefficientSupportProjection (Phi.val sigma.coefficients) with hSdef
  set A := boundedOperator (Phi.val rho.coefficients) with hAdef
  obtain ⟨ht, htt, htHS⟩ := sqrt_state (phiS Phi sigma)
  obtain ⟨hs, _, _⟩ := sqrt_state sigma
  have hcz : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hBx : ∀ x, t (B (t x)) = (c : ℂ) • A x := fun x => by
    have h := congrArg (fun T => T x) hB
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] at h
    exact h
  have hSt : ∀ u, S (t u) = t u := fun u =>
    Submodule.starProjection_eq_self_iff.mpr (mem_K t P ht htt u)
  have h0 : (ContinuousLinearMap.id ℂ (Hilbert J) - S).comp A = 0 := by
    ext1 x
    have h1 : (c : ℂ) • ((ContinuousLinearMap.id ℂ (Hilbert J) - S) (A x)) = 0 := by
      rw [← map_smul, ← hBx]
      simp [hSt]
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h hcz
    · simpa using h
  refine op_ext (funext fun a => funext fun b => ?_)
  -- right-hand side
  have hab : rho.coefficients a b = boundedTracePair (Phi.val rho.coefficients)
      (petzExtendedDual Phi.val sigma.coefficients
        (boundedOperator (Matrix.single b a (1 : ℂ)))) := congrFun (congrFun hP a) b
  have hR : boundedOperator (Matrix.single b a (1 : ℂ)) = rk (bvec b) (bvec a) :=
    bO_eq (coeff_rk_bvec a b)
  set D := petzSupportedDual Phi.val sigma.coefficients (rk (bvec b) (bvec a)) with hDdef
  have hDt := (dual_rk Phi sigma (bvec b) (bvec a)).2
  have hext : (petzExtendedDual Phi.val sigma.coefficients (rk (bvec b) (bvec a))).comp A =
      D.comp A := by
    simp only [petzExtendedDual, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp]
    rw [← hSdef, h0, smul_zero, add_zero]
  have hrhs : operatorCoeff ((c : ℂ) • boundedOperator rho.coefficients) a b =
      ∑' i, inner ℂ (bvec i) ((D.comp t) ((B.comp t) (bvec i))) := by
    rw [coeff_smul, Matrix.smul_apply, smul_eq_mul, coeff_bO rho.density.1, hab, hR]
    unfold boundedTracePair
    rw [← hAdef, hext, ← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    rw [operatorCoeff_apply, inner_bvec_left]
    simp only [ContinuousLinearMap.comp_apply, hBx, map_smul]
    rfl
  -- left-hand side
  have hlhs : operatorCoeff (s.comp ((channelDual Phi.val B).comp s)) a b =
      ∑' k, inner ℂ (bvec k) ((B.comp t) ((D.comp t) (bvec k))) := by
    rw [operatorCoeff_apply, coord_eq_inner]
    change inner ℂ (bvec a) (s (channelDual Phi.val B (s (bvec b)))) = _
    rw [sa_swap hs, channelDual_inner]
    unfold dF dG boundedTracePair
    rw [← hDt]
    refine tsum_congr (fun k => ?_)
    rw [operatorCoeff_apply, inner_bvec_left]
    rfl
  rw [hlhs, hrhs]
  exact (tr_cyc (B.comp t) (D.comp t) (hs_col B t htHS.summable) (hs_col D t htHS.summable)).symm








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

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)
open P45Petz P45N0 P45N1



end P45N1A

end

end N1Asm

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


open QAlgorithms.Papers.Independent.Gap48.P45 QAlgorithms.Papers.Independent.Dependency50.P33 QAlgorithms.Papers.Independent.Frontier18.P01 QAlgorithms.Papers.Independent.Frontier18.P18 in open QAlgorithms.RealRegisters (Hilbert) in open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
theorem solution {I J : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho sigma : State I)
    (hP : rho.coefficients = petzRecovery Phi.val sigma.coefficients (Phi.val rho.coefficients))
    (B : Hilbert J →L[ℂ] Hilbert J) (c : ℝ) (hc : 0 < c)
    (hB : (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients))).comp
        (B.comp (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)))) =
      (c : ℂ) • boundedOperator (Phi.val rho.coefficients)) :
    (positiveSquareRoot (boundedOperator sigma.coefficients)).comp
        ((channelDual Phi.val B).comp (positiveSquareRoot (boundedOperator sigma.coefficients))) =
      (c : ℂ) • boundedOperator rho.coefficients := by
  exact P45N1.n1c Phi rho sigma hP B c hc hB

end

end ChildRoot
