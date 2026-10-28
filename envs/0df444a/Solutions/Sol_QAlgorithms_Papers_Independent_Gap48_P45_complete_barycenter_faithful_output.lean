-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.complete_barycenter_faithful_output
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:39:27.404569+00:00
-- url     : https://prove2.me/submissions/35b8ad43-8ccf-4de5-a1e6-c7bfdaefd704

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

lemma tc_mat {T : Type} (w : ℕ → Hilbert T) (hw : Summable (fun n => ‖w n‖ ^ 2)) :
    IsTraceClass (Mat w) := by
  have h : IsTraceClass ((1:ℂ) • Mat w) := ⟨matExp 1 w hw⟩
  rwa [one_smul] at h


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

/-- Tr(B t t) = Tr(t B t) for a self-adjoint Hilbert-Schmidt t and bounded B. -/
lemma hs_cyc {T : Type} (t B : Hilbert T →L[ℂ] Hilbert T) (ht : ContinuousLinearMap.adjoint t = t)
    (hHS : Summable (fun k => ‖t (bvec k)‖ ^ 2)) :
    (∑' i, inner ℂ (bvec i) (B (t (t (bvec i))))) =
      ∑' k, inner ℂ (t (bvec k)) (B (t (bvec k))) := by
  set u : T → Hilbert T := fun k => t (bvec k) with hu
  set v : T → Hilbert T := fun i => t (ContinuousLinearMap.adjoint B (bvec i)) with hv
  have hu_sw : ∀ i k, u i k = star (u k i) := by
    intro i k
    simp only [hu]
    rw [coord_eq_inner (t (bvec i)) k, sa_swap ht, ← inner_conj_symm, inner_bvec_left]
    rfl
  have hBu : ∀ k i, (B (u k)) i = star (v i k) := by
    intro k i
    simp only [hu, hv]
    rw [coord_eq_inner (B _) i, ← ContinuousLinearMap.adjoint_inner_left, sa_swap ht,
      ← inner_conj_symm, inner_bvec_left]
    rfl
  have hL : ∀ i, inner ℂ (bvec i) (B (t (t (bvec i)))) = ∑' k, star (v i k) * star (u k i) := by
    intro i
    rw [← ContinuousLinearMap.adjoint_inner_left, sa_swap ht, inner_eq_tsum']
    refine tsum_congr (fun k => ?_)
    rw [← hu_sw i k]
  have hR : ∀ k, inner ℂ (t (bvec k)) (B (t (bvec k))) = ∑' i, star (u k i) * star (v i k) := by
    intro k
    rw [inner_eq_tsum']
    refine tsum_congr (fun i => ?_)
    rw [← hBu k i]
  rw [tsum_congr hL, tsum_congr hR]
  have hS1 : Summable (Function.uncurry (fun i k => ‖v i k‖ ^ 2)) := by
    have h := summable_uncurry_of_swap (fun i k => ‖(B (u k)) i‖ ^ 2)
      (fun _ _ => sq_nonneg _) (fun k => (hasSum_normSq (B (u k))).summable) (by
        refine Summable.of_nonneg_of_le (fun k => tsum_nonneg (fun _ => sq_nonneg _))
          (fun k => ?_) (hHS.mul_left (‖B‖ ^ 2))
        rw [(hasSum_normSq (B (u k))).tsum_eq, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2)
    refine h.congr (fun p => ?_)
    simp only [Function.uncurry]
    rw [hBu, norm_star]
  have hS2 : Summable (Function.uncurry (fun i k => ‖u k i‖ ^ 2)) := by
    refine summable_uncurry_of_swap (fun i k => ‖u k i‖ ^ 2) (fun _ _ => sq_nonneg _)
      (fun k => (hasSum_normSq (u k)).summable) ?_
    refine hHS.congr (fun k => ?_)
    rw [(hasSum_normSq (u k)).tsum_eq]
  rw [tsum_swap_of (fun i k => star (v i k) * star (u k i)) (fun i k => ‖v i k‖ ^ 2 + ‖u k i‖ ^ 2)
    (fun i k => by
      rw [norm_mul, norm_star, norm_star]
      nlinarith [norm_nonneg (v i k), norm_nonneg (u k i), sq_nonneg (‖v i k‖ - ‖u k i‖),
        mul_nonneg (norm_nonneg (v i k)) (norm_nonneg (u k i))])
    (hS1.add hS2)]
  exact tsum_congr (fun k => tsum_congr (fun i => mul_comm _ _))

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

/-- boundedTracePair through a self-adjoint Hilbert-Schmidt square root. -/
lemma tracePair_cyc {T : Type} (X : Matrix T T ℂ) (t B : Hilbert T →L[ℂ] Hilbert T)
    (ht : ContinuousLinearMap.adjoint t = t) (htt : t * t = boundedOperator X)
    (hHS : Summable (fun k => ‖t (bvec k)‖ ^ 2)) :
    boundedTracePair X B = ∑' k, inner ℂ (t (bvec k)) (B (t (bvec k))) := by
  rw [← hs_cyc t B ht hHS]
  unfold boundedTracePair
  refine tsum_congr (fun i => ?_)
  rw [inner_bvec_left, ← htt]
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



lemma bO_zero {T : Type} : boundedOperator (0 : Matrix T T ℂ) = 0 :=
  bO_eq (by funext i j; simp [operatorCoeff])

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


lemma chan_fsum {I J ι : Type} (Phi : Channel I J) (F : Finset ι) (Y : ι → Matrix I I ℂ)
    (hY : ∀ i, IsTraceClass (Y i)) :
    IsTraceClass (∑ i ∈ F, Y i) ∧ Phi.val (∑ i ∈ F, Y i) = ∑ i ∈ F, Phi.val (Y i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using ⟨tc_zero, chan_zero Phi⟩
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨tc_add (hY a) ih.1, by rw [Phi.property.2.1 _ _ (hY a) ih.1, ih.2]⟩

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
noncomputable local instance (priority := 1100) scC_acm_5 {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] : AddCommMonoid (E →L[ℂ] F) := inferInstance
noncomputable local instance (priority := 1100) scH_am_5 (X : Type) : AddMonoid (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_azc_5 (X : Type) : AddZeroClass (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_snacg_5 (X : Type) : SeminormedAddCommGroup (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scH_us_5 (X : Type) : UniformSpace (QAlgorithms.RealRegisters.Hilbert X) := inferInstance
noncomputable local instance (priority := 1100) scHC_acm_5 (X Y : Type) : AddCommMonoid (QAlgorithms.RealRegisters.Hilbert X →L[ℂ] QAlgorithms.RealRegisters.Hilbert Y) := inferInstance
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

lemma hasSum_ite_compl {α : Type} [NormedAddCommGroup α] {f : ℕ → α} (hf : Summable f)
    (F : Finset ℕ) :
    HasSum (fun n => if n ∈ F then 0 else f n) (∑' n, f n - ∑ n ∈ F, f n) := by
  have hg : HasSum (fun n => if n ∈ F then f n else 0) (∑ n ∈ F, f n) := by
    have : HasSum (fun n => if n ∈ F then f n else 0) (∑ b ∈ F, (if b ∈ F then f b else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
    convert this using 1
    exact (Finset.sum_congr rfl (fun n hn => by simp [hn])).symm
  have h := hf.hasSum.sub hg
  convert h using 1
  funext n
  by_cases hn : n ∈ F <;> simp [hn]

lemma coeff_fsum (F : Finset ℕ) (R : ℕ → Hilbert I →L[ℂ] Hilbert I) :
    operatorCoeff (∑ n ∈ F, R n) = ∑ n ∈ F, operatorCoeff (R n) := by
  induction F using Finset.induction_on with
  | empty => funext i j; simp [operatorCoeff]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

lemma pair_fsum {T ι : Type} (B : Hilbert T →L[ℂ] Hilbert T) (F : Finset ι)
    (Y : ι → Matrix T T ℂ) (hY : ∀ i, IsTraceClass (Y i)) :
    boundedTracePair (∑ i ∈ F, Y i) B = ∑ i ∈ F, boundedTracePair (Y i) B := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have h := pair_smul B 0 (tc_zero (T := T))
    simp only [zero_smul] at h
    simpa using h
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add B (hY a) (tc_fsum F Y hY), ih]

lemma dG_fsum (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (F : Finset ℕ)
    (R : ℕ → Hilbert I →L[ℂ] Hilbert I) (hR : ∀ n, IsTraceClass (operatorCoeff (R n))) :
    dG Phi W (∑ n ∈ F, R n) = ∑ n ∈ F, dG Phi W (R n) := by
  induction F using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, dG_zero]
  | insert a F ha ih =>
    have htc : IsTraceClass (operatorCoeff (∑ n ∈ F, R n)) := by
      rw [coeff_fsum]; exact tc_fsum F _ hR
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dG_add _ _ _ _ (hR a) htc, ih]

lemma mat_split (v : ℕ → Hilbert I) (hv : Summable (fun n => ‖v n‖ ^ 2)) (F : Finset ℕ) :
    Mat v = operatorCoeff (∑ n ∈ F, rk (v n) (v n)) + Mat (fun n => if n ∈ F then 0 else v n) := by
  funext i j
  rw [coeff_fsum, Matrix.add_apply, Matrix.sum_apply]
  simp only [Mat, coeff_rk]
  have hf := mat_coeff_summable v hv i j
  have h := hasSum_ite_compl hf F
  have e : (fun n => (if n ∈ F then 0 else v n) i * star ((if n ∈ F then 0 else v n) j)) =
      fun n => if n ∈ F then 0 else v n i * star (v n j) := by
    funext n; by_cases hn : n ∈ F <;> simp [hn]
  rw [e, h.tsum_eq]
  ring

lemma pair_mat_bound (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (v : ℕ → Hilbert I)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    ‖boundedTracePair (Phi.val (Mat v)) W‖ ≤ ‖W‖ * ∑' n, ‖v n‖ ^ 2 := by
  have hs0 : 0 ≤ ∑' n, ‖v n‖ ^ 2 := tsum_nonneg (fun n => sq_nonneg _)
  by_cases h0 : (∑' n, ‖v n‖ ^ 2) = 0
  · have hf := (hasSum_zero_iff_of_nonneg (fun n => sq_nonneg ‖v n‖)).mp (h0 ▸ hv.hasSum)
    have hv0 : ∀ n, v n = 0 := fun n => by
      have := congrFun hf n
      simpa using this
    have hM : Mat v = 0 := by funext i j; simp [Mat, hv0]
    have h := pair_smul W 0 (tc_zero (T := J))
    simp only [zero_smul] at h
    rw [hM, chan_zero Phi, h0, h]
    simp
  · have hd := chan_density Phi.val Phi.property _ (isDensity_mat v hv h0)
    have hb := pair_state_bound ⟨_, hd⟩ W
    have e : Mat v = (((∑' n, ‖v n‖ ^ 2 : ℝ)) : ℂ) •
        ((((∑' n, ‖v n‖ ^ 2)⁻¹ : ℝ) : ℂ) • Mat v) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one, one_smul]
    have htc : IsTraceClass ((((∑' n, ‖v n‖ ^ 2)⁻¹ : ℝ) : ℂ) • Mat v) := tc_smul _ (tc_mat v hv)
    rw [e, Phi.property.2.2.1 _ _ htc, pair_smul W _ (Phi.property.1 _ htc), smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    nlinarith [mul_le_mul_of_nonneg_left hb hs0]

/-- Normality on positive pieces: Tr(Phi(Mat v) W) = Sum_n Tr(Phi(|v_n><v_n|) W). -/
theorem pair_mat_hasSum (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (v : ℕ → Hilbert I)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    HasSum (fun n => dF Phi W (v n) (v n)) (boundedTracePair (Phi.val (Mat v)) W) := by
  have htl : ∀ F : Finset ℕ, Summable (fun n => ‖(if n ∈ F then 0 else v n : Hilbert I)‖ ^ 2) := by
    intro F
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hv
    by_cases hn : n ∈ F <;> simp [hn]
  have hsplit : ∀ F : Finset ℕ, boundedTracePair (Phi.val (Mat v)) W -
      ∑ n ∈ F, dF Phi W (v n) (v n) =
      boundedTracePair (Phi.val (Mat (fun n => if n ∈ F then 0 else v n))) W := by
    intro F
    have htc1 : IsTraceClass (operatorCoeff (∑ n ∈ F, rk (v n) (v n))) := by
      rw [coeff_fsum]; exact tc_fsum F _ (fun n => tc_rk _ _)
    have htc2 := tc_mat _ (htl F)
    have hsum : ∑ n ∈ F, dF Phi W (v n) (v n) = dG Phi W (∑ n ∈ F, rk (v n) (v n)) :=
      (dG_fsum Phi W F _ (fun n => tc_rk _ _)).symm
    rw [hsum, mat_split v hv F, Phi.property.2.1 _ _ htc1 htc2,
      pair_add W (Phi.property.1 _ htc1) (Phi.property.1 _ htc2)]
    unfold dG
    ring
  have htail : ∀ F : Finset ℕ, ∑' n, ‖(if n ∈ F then 0 else v n : Hilbert I)‖ ^ 2 =
      ∑' n, ‖v n‖ ^ 2 - ∑ n ∈ F, ‖v n‖ ^ 2 := by
    intro F
    have h := hasSum_ite_compl hv F
    rw [← h.tsum_eq]
    congr 1
    funext n
    by_cases hn : n ∈ F <;> simp [hn]
  unfold HasSum
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun F : Finset ℕ => ‖W‖ * (∑' n, ‖v n‖ ^ 2 - ∑ n ∈ F, ‖v n‖ ^ 2))
    (fun F => norm_nonneg _) (fun F => ?_) ?_
  · rw [norm_sub_rev, hsplit F, ← htail F]
    exact pair_mat_bound Phi W _ (htl F)
  · have h1 : Filter.Tendsto (fun F : Finset ℕ => ∑' n, ‖v n‖ ^ 2 - ∑ n ∈ F, ‖v n‖ ^ 2)
        Filter.atTop (nhds (∑' n, ‖v n‖ ^ 2 - ∑' n, ‖v n‖ ^ 2)) :=
      tendsto_const_nhds.sub hv.hasSum
    rw [sub_self] at h1
    have h2 := h1.const_mul ‖W‖
    rwa [mul_zero] at h2

theorem dual_mat (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (v : ℕ → Hilbert I)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    boundedTracePair (Mat v) (channelDual Phi.val W) = boundedTracePair (Phi.val (Mat v)) W := by
  have hs : Summable (fun n => ‖v n‖ * ‖v n‖) := by simpa [sq] using hv
  have hX : ∀ i j, HasSum (fun k => v k i * star (v k j)) (Mat v i j) :=
    fun i j => (mat_coeff_summable v hv i j).hasSum
  have h1 := pair_gen (channelDual Phi.val W) v v hs hX
  simp_rw [channelDual_inner] at h1
  exact h1.unique (pair_mat_hasSum Phi W v hv)

/-- K-c duality: Tr(X Phi*(W)) = Tr(Phi(X) W) for every trace-class X. -/
theorem dual_pair (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) (X : Matrix I I ℂ)
    (hX : IsTraceClass X) :
    boundedTracePair X (channelDual Phi.val W) = boundedTracePair (Phi.val X) W := by
  obtain ⟨e0⟩ := hX
  obtain ⟨e, he⟩ := balance e0
  have hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖ := fun n => by
    have h : ‖e.left n‖ ^ 2 = ‖e.right n‖ ^ 2 := (he n).1.trans (he n).2.symm
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have hM : ∀ c, IsTraceClass (Mat (wc e c)) := fun c => tc_mat _ (wc_summable e hbal c)
  have hY : ∀ c, IsTraceClass ((Complex.I ^ c / 4) • Mat (wc e c)) := fun c => tc_smul _ (hM c)
  rw [polar_split e hbal, (chan_fsum Phi _ _ hY).2, pair_fsum _ _ _ hY,
    pair_fsum _ _ _ (fun c => Phi.property.1 _ (hY c))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Phi.property.2.2.1 _ _ (hM c), pair_smul _ _ (hM c), pair_smul _ _ (Phi.property.1 _ (hM c)),
    dual_mat Phi W _ (wc_summable e hbal c)]


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



lemma nonneg_adj {C : E →L[ℂ] E} (hC : 0 ≤ C) : ContinuousLinearMap.adjoint C = C := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive C).mp hC).isSelfAdjoint





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









lemma bTP_rk {T : Type} (M : Matrix T T ℂ) (x y : Hilbert T) :
    boundedTracePair M (rk y x) = inner ℂ x (boundedOperator M y) := by
  unfold boundedTracePair
  set P := boundedOperator M
  have h1 : ∀ l, operatorCoeff ((rk y x).comp P) l l =
      star ((ContinuousLinearMap.adjoint P x) l) * y l := by
    intro l
    rw [operatorCoeff_apply, ContinuousLinearMap.comp_apply, rk_apply]
    have h2 : star ((ContinuousLinearMap.adjoint P x) l) = inner ℂ x (P (lp.single 2 l 1)) := by
      rw [coord_eq_inner, ContinuousLinearMap.adjoint_inner_right]
      show (starRingEnd ℂ) (inner ℂ (P (bvec l)) x) = _
      rw [inner_conj_symm]
      rfl
    rw [h2]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [tsum_congr h1, ← inner_eq_tsum', ContinuousLinearMap.adjoint_inner_left]

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

lemma rk_img_pos {I J : Type} (Phi : Channel I J) (u : Hilbert I) :
    (boundedOperator (Phi.val (operatorCoeff (rk u u)))).IsPositive := by
  rcases eq_or_ne u 0 with rfl | hu
  · have h0 : operatorCoeff (rk (0 : Hilbert I) 0) = 0 := by
      funext i j; simp [operatorCoeff, rk_apply]
    rw [h0, chan_zero, bO_zero]
    exact (ContinuousLinearMap.nonneg_iff_isPositive 0).mp le_rfl
  · set c : ℝ := ‖u‖ with hc
    have hc0 : 0 < c := norm_pos_iff.mpr hu
    set u' : Hilbert I := ((c⁻¹ : ℝ) : ℂ) • u with hu'
    have hn : ‖u'‖ = 1 := by
      rw [hu', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0,
        inv_mul_cancel₀ hc0.ne']
    have hu_eq : u = ((c : ℝ) : ℂ) • u' := by
      rw [hu', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc0.ne', Complex.ofReal_one, one_smul]
    have hd := isDensity_rk u' hn
    have hrk : rk u u = ((c : ℂ) * star (c : ℂ)) • rk u' u' := by
      conv_lhs => rw [hu_eq]
      exact rk_smul_smul _ _ _
    rw [hrk, coeff_smul, Phi.property.2.2.1 _ _ hd.1, bO_smul _ (Phi.property.1 _ hd.1)]
    have hcc : ((c : ℂ) * star (c : ℂ)) = ((c ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [hcc]
    exact (bO_pos (phiS Phi ⟨operatorCoeff (rk u' u'), hd⟩)).smul_of_nonneg
      (by exact_mod_cast sq_nonneg c)

open P45C4B in
lemma dual_rk_pos {I J : Type} (Phi : Channel I J) (y : Hilbert J) :
    (channelDual Phi.val (rk y y)).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hf : inner ℂ x (channelDual Phi.val (rk y y) x) =
      inner ℂ y (boundedOperator (Phi.val (operatorCoeff (rk x x))) y) := by
    rw [channelDual_inner]; unfold dF dG; exact bTP_rk _ y y
  have hn := (rk_img_pos Phi x).toLinearMap.inner_nonneg_right y
  simp only [ContinuousLinearMap.coe_coe] at hn
  rw [← inner_conj_symm (channelDual Phi.val (rk y y) x) x, hf]
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  generalize inner ℂ y (boundedOperator (Phi.val (operatorCoeff (rk x x))) y) = z at hre him ⊢
  constructor
  · apply Complex.ext <;> simp [← him]
  · simpa using hre

open P45C4B in
/-- N1a(ii): for a faithful barycenter the output support is the support of Phi(sigma). -/
theorem out_eq {I J L : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) {pi : L → ℝ} (hpi : PositiveLaw pi) (sigma : State I)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    outputProjection Phi.val = coefficientSupportProjection (Phi.val sigma.coefficients) := by
  have hfaith := faithful rho hC hpi sigma hbar
  set P := boundedOperator (Phi.val sigma.coefficients) with hPdef
  set K := (LinearMap.range P.toLinearMap).topologicalClosure with hK
  obtain ⟨hs, hss, hsHS⟩ := sqrt_state sigma
  set s := positiveSquareRoot (boundedOperator sigma.coefficients) with hsdef
  have hgen : ∀ (ρ : State I) (w : Hilbert J), boundedOperator (Phi.val ρ.coefficients) w ∈ K := by
    intro ρ w
    rw [← Submodule.orthogonal_orthogonal K, Submodule.mem_orthogonal]
    intro y hy
    have hPy : inner ℂ y (P y) = 0 := by
      have h : inner ℂ (P y) y = 0 := Submodule.inner_right_of_mem_orthogonal
        (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self P.toLinearMap y)) hy
      rw [← inner_conj_symm, h, map_zero]
    have hApos := dual_rk_pos Phi y
    have htr : boundedTracePair sigma.coefficients (channelDual Phi.val (rk y y)) = 0 := by
      rw [dual_pair Phi _ _ sigma.density.1, bTP_rk]
      exact hPy
    have hcyc := tracePair_cyc sigma.coefficients s (channelDual Phi.val (rk y y)) hs hss
      hsHS.summable
    rw [htr] at hcyc
    set A := channelDual Phi.val (rk y y) with hA
    have hterm : ∀ k, A (s (bvec k)) = 0 := by
      have hnn : ∀ k, 0 ≤ (inner ℂ (s (bvec k)) (A (s (bvec k)))).re := fun k =>
        hApos.re_inner_nonneg_right _
      have hS : Summable (fun k => inner ℂ (s (bvec k)) (A (s (bvec k)))) := by
        refine Summable.of_norm_bounded (hsHS.summable.mul_left ‖A‖) (fun k => ?_)
        refine (norm_inner_le_norm _ _).trans ?_
        calc ‖s (bvec k)‖ * ‖A (s (bvec k))‖ ≤ ‖s (bvec k)‖ * (‖A‖ * ‖s (bvec k)‖) :=
              mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
          _ = ‖A‖ * ‖s (bvec k)‖ ^ 2 := by ring
      have hre : HasSum (fun k => (inner ℂ (s (bvec k)) (A (s (bvec k)))).re) 0 := by
        have h := (hS.hasSum.mapL Complex.reCLM)
        rw [← hcyc] at h
        simpa using h
      have hz := (hasSum_zero_iff_of_nonneg hnn).mp hre
      intro k
      exact pos_form_zero A hApos _ (congrFun hz k)
    have hAs : A.comp s = 0 := by
      refine op_ext (funext fun i => funext fun j => ?_)
      rw [operatorCoeff_apply, operatorCoeff_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply]
      exact congrArg (fun v : Hilbert I => v i) (hterm j)
    have hA0 : A = 0 := by
      have hRperp : (LinearMap.range s.toLinearMap)ᗮ = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro v hv
        have h1 : s v = 0 := by
          rw [← inner_self_eq_zero (𝕜 := ℂ)]
          have h := Submodule.inner_right_of_mem_orthogonal
            (LinearMap.mem_range_self s.toLinearMap (s v)) hv
          rw [sa_swap hs]
          exact h
        exact hfaith v (by rw [← hss, ContinuousLinearMap.mul_apply, h1, map_zero])
      have hcl : (LinearMap.range s.toLinearMap).topologicalClosure = ⊤ := by
        rw [← Submodule.orthogonal_orthogonal_eq_closure, hRperp, Submodule.bot_orthogonal_eq_top]
      have hle : LinearMap.range s.toLinearMap ≤ LinearMap.ker (A : Hilbert I →ₗ[ℂ] Hilbert I) := by
        rintro _ ⟨w, rfl⟩
        have := congrArg (fun T : Hilbert I →L[ℂ] Hilbert I => T w) hAs
        simpa using this
      have hk := Submodule.topologicalClosure_minimal _ hle A.isClosed_ker
      rw [hcl] at hk
      ext1 z
      exact hk Submodule.mem_top
    have hA0' : channelDual Phi.val (rk y y) = 0 := hA0
    have hρ : inner ℂ y (boundedOperator (Phi.val ρ.coefficients) y) = 0 := by
      rw [← bTP_rk, ← dual_pair Phi (rk y y) ρ.coefficients ρ.density.1, hA0']
      simp [boundedTracePair, operatorCoeff]
    have hρy : boundedOperator (Phi.val ρ.coefficients) y = 0 :=
      pos_form_zero (boundedOperator (Phi.val ρ.coefficients)) (bO_pos (phiS Phi ρ)) y
        (by rw [hρ, Complex.zero_re])
    have hsa : ContinuousLinearMap.adjoint (boundedOperator (Phi.val ρ.coefficients)) =
        boundedOperator (Phi.val ρ.coefficients) :=
      nonneg_adj ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (bO_pos (phiS Phi ρ)))
    rw [← ContinuousLinearMap.adjoint_inner_left, hsa, hρy, inner_zero_left]
  have hO : outputSpace Phi.val = K := by
    apply le_antisymm
    · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
      rw [Submodule.span_le]
      rintro _ ⟨ρ, w, rfl⟩
      exact hgen ρ w
    · refine Submodule.topologicalClosure_mono ?_
      rintro _ ⟨w, rfl⟩
      exact Submodule.subset_span ⟨sigma, w, rfl⟩
  unfold outputProjection coefficientSupportProjection
  congr 1
  all_goals first | exact hO | exact proof_irrel_heq _ _

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


open QAlgorithms.Papers.Independent.Gap48.P45 QAlgorithms.Papers.Independent.Dependency50.P33 QAlgorithms.Papers.Independent.Frontier18.P01 QAlgorithms.Papers.Independent.Frontier18.P18 QAlgorithms.Papers.Independent.Next46.P31 in
theorem solution {I J L : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) (pi : L → ℝ) (hpi : PositiveLaw pi) (sigma : State I)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    outputProjection Phi.val = coefficientSupportProjection (Phi.val sigma.coefficients) ∧
      Function.Injective (positiveSquareRoot (boundedOperator sigma.coefficients)) ∧
      DenseRange (positiveSquareRoot (boundedOperator sigma.coefficients)) := by
  exact ⟨P45N1.out_eq Phi rho hC hpi sigma hbar, P45N1A.sqrt_inj_dense rho hC hpi sigma hbar⟩

end

end ChildRoot
