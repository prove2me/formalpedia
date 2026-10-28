-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.barycenter_douglas_resolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:27:52.017155+00:00
-- url     : https://prove2.me/submissions/a02b2e4d-9557-45ad-b622-c2d9720ec7c5

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

lemma dens_diag_hasSum {T : Type} {D : Matrix T T ℂ} (hD : IsDensity D) :
    HasSum (fun i => D i i) 1 := by
  obtain ⟨_, hq, hs, ht⟩ := hD
  have him : ∀ i, (D i i).im = 0 := by
    intro i
    have h := (hq {i} (fun _ => 1)).1
    simpa using h
  have hre : HasSum (fun i => ((D i i).re : ℂ)) ((1 : ℝ) : ℂ) := by
    rw [← ht]; exact Complex.hasSum_ofReal.mpr hs.hasSum
  have heq : (fun i => D i i) = fun i => ((D i i).re : ℂ) := by
    funext i; exact Complex.ext (by simp) (by simp [him i])
  rw [heq]; simpa using hre

lemma chan_mat_trace {I J : Type} (Phi : Channel I J) (w : ℕ → Hilbert I)
    (hw : Summable (fun n => ‖w n‖ ^ 2)) :
    HasSum (fun i => Mat w i i) ((∑' n, ‖w n‖ ^ 2 : ℝ) : ℂ) ∧
    HasSum (fun j => Phi.val (Mat w) j j) ((∑' n, ‖w n‖ ^ 2 : ℝ) : ℂ) := by
  by_cases hs : (∑' n, ‖w n‖ ^ 2) = 0
  · have h0 := (hasSum_zero_iff_of_nonneg (fun n => sq_nonneg ‖w n‖)).mp (hs ▸ hw.hasSum)
    have hw0 : ∀ n, w n = 0 := fun n => by
      have := congrFun h0 n; simpa using this
    have hM : Mat w = 0 := by funext i j; simp [Mat, hw0]
    rw [hM, chan_zero, hs]
    simp only [Complex.ofReal_zero, Matrix.zero_apply]
    exact ⟨hasSum_zero, hasSum_zero⟩
  · set s := ∑' n, ‖w n‖ ^ 2 with hsdef
    set c : ℂ := ((s⁻¹ : ℝ) : ℂ) with hc
    have hsc : (s : ℂ) * c = 1 := by
      rw [hc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one]
    have hD := isDensity_mat w hw hs
    have hMs : Mat w = ((s : ℂ)) • (c • Mat w) := by rw [smul_smul, hsc, one_smul]
    have h2 : Phi.val (Mat w) = ((s:ℂ)) • Phi.val (c • Mat w) := by
      conv_lhs => rw [hMs]
      exact Phi.property.2.2.1 _ _ hD.1
    have hP := dens_diag_hasSum (chan_density Phi.val Phi.property _ hD)
    have hQ := dens_diag_hasSum hD
    constructor
    · have h3 := hQ.mul_left (s : ℂ)
      rw [mul_one] at h3
      have hf : (fun i => Mat w i i) = fun i => (s : ℂ) * (c • Mat w) i i := by
        funext i
        rw [show Mat w i i = (((s : ℂ)) • (c • Mat w)) i i from congrFun (congrFun hMs i) i]
        rfl
      rw [hf]; exact h3
    · have h3 := hP.mul_left (s : ℂ)
      rw [mul_one] at h3
      rw [h2]
      exact h3

lemma chan_trace {I J : Type} (Phi : Channel I J) {X : Matrix I I ℂ} (hX : IsTraceClass X) :
    ∃ t : ℂ, HasSum (fun i => X i i) t ∧ HasSum (fun j => Phi.val X j j) t := by
  obtain ⟨e0⟩ := hX
  obtain ⟨e, he⟩ := balance e0
  have hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖ := fun n =>
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ((he n).1.trans (he n).2.symm)
  have hsplit := polar_split e hbal
  refine ⟨∑ c ∈ Finset.range 4, (Complex.I ^ c / 4) * ((∑' n, ‖wc e c n‖ ^ 2 : ℝ) : ℂ), ?_, ?_⟩
  · have h := hasSum_sum (s := Finset.range 4) (fun c _ =>
      ((chan_mat_trace Phi (wc e c) (wc_summable e hbal c)).1.mul_left (Complex.I ^ c / 4)))
    have hf : (fun i => X i i) =
        fun b => ∑ i ∈ Finset.range 4, Complex.I ^ i / 4 * Mat (wc e i) b b := by
      funext i
      rw [show X i i = _ from congrFun (congrFun hsplit i) i, Matrix.sum_apply]
      rfl
    rw [hf]; exact h
  · have hPX : Phi.val X = ∑ c ∈ Finset.range 4, (Complex.I ^ c / 4) • Phi.val (Mat (wc e c)) :=
      (congrArg Phi.val hsplit).trans
        (chan_sum Phi 4 _ _ (fun c => tc_mat _ (wc_summable e hbal c)))
    have h := hasSum_sum (s := Finset.range 4) (fun c _ =>
      ((chan_mat_trace Phi (wc e c) (wc_summable e hbal c)).2.mul_left (Complex.I ^ c / 4)))
    have hf : (fun j => Phi.val X j j) =
        fun b => ∑ i ∈ Finset.range 4, Complex.I ^ i / 4 * Phi.val (Mat (wc e i)) b b := by
      funext j
      rw [hPX, Matrix.sum_apply]
      rfl
    rw [hf]; exact h



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

lemma K_sub {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (t P : E →L[ℂ] E) (htt : t * t = P) :
    ((LinearMap.range P.toLinearMap).topologicalClosure : Set E) ⊆ closure (Set.range t) := by
  rw [Submodule.topologicalClosure_coe]
  refine closure_mono ?_
  rintro _ ⟨u, rfl⟩
  refine ⟨t u, ?_⟩
  rw [← htt]; rfl

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





/-- The supported dual on the i-th diagonal matrix unit. -/
def Bi {I J : Type} (Phi : Channel I J) (sigma : State I) (i : I) : Hilbert J →L[ℂ] Hilbert J :=
  petzSupportedDual Phi.val sigma.coefficients (rk (bvec i) (bvec i))

/-- Support projection minus the partial sums of the diagonal supported duals. -/
def TF {I J : Type} (Phi : Channel I J) (sigma : State I) (F : Finset I) :
    Hilbert J →L[ℂ] Hilbert J :=
  coefficientSupportProjection (Phi.val sigma.coefficients) - ∑ i ∈ F, Bi Phi sigma i








lemma par_bound {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T : E →L[ℂ] E)
    (hpos : ∀ z, 0 ≤ (inner ℂ z (T z)).re) (hle : ∀ z, (inner ℂ z (T z)).re ≤ ‖z‖ ^ 2) (x y : E) :
    (inner ℂ x (T x)).re ≤ 2 * (inner ℂ y (T y)).re + 2 * ‖x - y‖ ^ 2 := by
  have hid : ∀ a b : E, inner ℂ (a + b) (T (a + b)) + inner ℂ (a - b) (T (a - b)) =
      (inner ℂ a (T a) + inner ℂ a (T a)) + (inner ℂ b (T b) + inner ℂ b (T b)) := by
    intro a b
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    ring
  have h := congrArg Complex.re (hid y (x - y))
  have e : y + (x - y) = x := by abel
  rw [e] at h
  simp only [Complex.add_re] at h
  linarith [hpos (y - (x - y)), hle (x - y)]













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

lemma form_smul {T : Type} (r : ℝ) (M : Matrix T T ℂ) (s : Finset T) (z : T → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * (((r : ℂ)) • M) i j * z j) =
      (r : ℂ) * ∑ i ∈ s, ∑ j ∈ s, star (z i) * M i j * z j := by
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma scale_form (r : ℝ) (hr : 0 ≤ r) (w : ℂ) (h : w.im = 0 ∧ 0 ≤ w.re) :
    ((r : ℂ) * w).im = 0 ∧ 0 ≤ ((r : ℂ) * w).re := by
  constructor
  · simp [Complex.mul_im, h.1]
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hr h.2

lemma psd_zero_of_diag {T : Type} {M : Matrix T T ℂ} (hM : PSDForms M)
    (hd : ∀ i, (M i i).re = 0) : M = 0 := by
  ext i j
  have h := psd_cs hM i j
  rw [hd i, hd j, mul_zero] at h
  have h2 : ‖M i j‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  rw [Matrix.zero_apply]
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

/-- A channel maps positive trace-class operators to operators with positive finite forms. -/
lemma chan_psd {I J : Type} (Φ : Channel I J) {M : Matrix I I ℂ} (hM : PSDForms M)
    (htc : IsTraceClass M) (hd : Summable (fun i => (M i i).re)) : PSDForms (Φ.val M) := by
  set c := ∑' i, (M i i).re with hc
  have hc0 : 0 ≤ c := tsum_nonneg (fun i => (psd_diag hM i).2)
  rcases eq_or_lt_of_le hc0 with h0 | hpos
  · have h0' : HasSum (fun i => (M i i).re) 0 := by rw [h0]; exact hd.hasSum
    have hz : M = 0 := psd_zero_of_diag hM (fun i =>
      congrFun ((hasSum_zero_iff_of_nonneg (fun i => (psd_diag hM i).2)).mp h0') i)
    rw [hz, chan_zero]
    intro s z; simp
  · have hD : IsDensity (((c⁻¹ : ℝ) : ℂ) • M) := by
      refine ⟨tc_smul _ htc, ?_, ?_, ?_⟩
      · intro s z
        rw [form_smul]
        exact scale_form _ (inv_nonneg.mpr hc0) _ (hM s z)
      · simpa [Matrix.smul_apply] using hd.mul_left c⁻¹
      · simp only [Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        rw [tsum_mul_left, ← hc]; exact inv_mul_cancel₀ hpos.ne'
    have hP := chan_density Φ.val Φ.property _ hD
    have e : Φ.val M = ((c : ℝ) : ℂ) • Φ.val (((c⁻¹ : ℝ) : ℂ) • M) := by
      rw [Φ.property.2.2.1 _ _ htc, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne',
        Complex.ofReal_one, one_smul]
    intro s z
    rw [e, form_smul]
    exact scale_form _ hc0 _ (hP.2.1 s z)


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

lemma chan_wm_coef_le [Countable I] {J : Type} (Phi : Channel I J) {w : L → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w) (rho : L → State I) (a b : J) :
    ‖Phi.val (wm w rho) a b‖ ≤ ∑' j, w j := by
  have hpsd := wm_psd hw0 hw rho
  have hd := wm_diag_hasSum hw0 hw rho
  have htc := wm_tc hw0 hw rho
  obtain ⟨t, ht1, ht2⟩ := chan_trace Phi htc
  have hre1 := Complex.reCLM.hasSum ht1
  have hre2 := Complex.reCLM.hasSum ht2
  simp only [Complex.reCLM_apply] at hre1 hre2
  have htre : t.re = ∑' j, w j := hre1.unique hd
  rw [htre] at hre2
  exact psd_coef_le (chan_psd Phi hpsd htc hd.summable) hre2 a b

lemma chan_wm [Countable I] {J : Type} (Phi : Channel I J) {w : L → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w) (rho : L → State I) :
    Phi.val (wm w rho) = wm w (fun j => phiS Phi (rho j)) := by
  ext a b
  have key : ∀ F : Finset L, ‖(∑ j ∈ F, (w j : ℂ) * Phi.val (rho j).coefficients a b) -
      Phi.val (wm w rho) a b‖ ≤ ∑' j, w j - ∑ j ∈ F, w j := by
    intro F
    have hw'0 : ∀ j, 0 ≤ (if j ∈ F then 0 else w j) := fun j => by
      split_ifs
      · exact le_rfl
      · exact hw0 j
    have hw'h := compl_hasSum hw F
    have hsplit := wm_split hw rho F
    have hsm : ∀ j, IsTraceClass ((w j : ℂ) • (rho j).coefficients) :=
      fun j => tc_smul _ (rho j).density.1
    have hadd := Phi.property.2.1 _ _ (tc_fsum F _ hsm) (wm_tc hw'0 hw'h.summable rho)
    have hF := (chan_fsum Phi F (fun j => (w j : ℂ) • (rho j).coefficients) hsm).2
    have hb := chan_wm_coef_le Phi hw'0 hw'h.summable rho a b
    rw [hw'h.tsum_eq] at hb
    have hterm : ∀ j ∈ F, Phi.val ((w j : ℂ) • (rho j).coefficients) a b =
        (w j : ℂ) * Phi.val (rho j).coefficients a b := by
      intro j _
      rw [Phi.property.2.2.1 _ _ (rho j).density.1]
      rfl
    rw [hsplit, hadd, hF, Matrix.add_apply, Matrix.sum_apply, Finset.sum_congr rfl hterm,
      sub_add_cancel_left, norm_neg]
    exact hb
  have hT : Tendsto (fun F : Finset L => ∑ j ∈ F, (w j : ℂ) * Phi.val (rho j).coefficients a b)
      atTop (𝓝 (Phi.val (wm w rho) a b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun F => norm_nonneg _) key ?_
    have hw2 : Tendsto (fun F : Finset L => ∑ j ∈ F, w j) atTop (𝓝 (∑' j, w j)) := hw.hasSum
    simpa using (tendsto_const_nhds (x := ∑' j, w j)).sub hw2
  have hS : HasSum (fun j => (w j : ℂ) * Phi.val (rho j).coefficients a b)
      (Phi.val (wm w rho) a b) := hT
  exact hS.tsum_eq.symm


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

lemma cl_nonneg (t : E →L[ℂ] E) (f : E → ℝ) (hf : Continuous f) (h : ∀ u, 0 ≤ f (t u))
    {z : E} (hz : z ∈ closure (Set.range t)) : 0 ≤ f z := by
  have hc : IsClosed {z | 0 ≤ f z} := isClosed_le continuous_const hf
  have hsub : Set.range t ⊆ {z | 0 ≤ f z} := by rintro _ ⟨u, rfl⟩; exact h u
  exact closure_minimal hsub hc hz

lemma sp_adj (K : Submodule ℂ E) [K.HasOrthogonalProjection] :
    ContinuousLinearMap.adjoint K.starProjection = K.starProjection := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact isSelfAdjoint_starProjection _

lemma nonneg_adj {C : E →L[ℂ] E} (hC : 0 ≤ C) : ContinuousLinearMap.adjoint C = C := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive C).mp hC).isSelfAdjoint

lemma compress_form (K : Submodule ℂ E) [K.HasOrthogonalProjection] (B : E →L[ℂ] E)
    (hS : K.starProjection.comp (B.comp K.starProjection) = B) (x : E) :
    inner ℂ x (B x) = inner ℂ (K.starProjection x) (B (K.starProjection x)) := by
  conv_lhs => rw [← hS]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← Submodule.inner_starProjection_left_eq_right]

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

/-- Positivity of a compressed solution of `t B t = C` with `C ≥ 0`. -/
lemma pos_of_sandwich (t P B C : E →L[ℂ] E) (ht : ContinuousLinearMap.adjoint t = t)
    (htt : t * t = P)
    (hS : ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection).comp
          (B.comp ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection)) = B)
    (hB : t.comp (B.comp t) = C) (hC : 0 ≤ C) (x : E) : 0 ≤ (inner ℂ x (B x)).re := by
  rw [compress_form _ B hS x]
  refine cl_nonneg t (fun z => (inner ℂ z (B z)).re)
    (Complex.continuous_re.comp (continuous_id.inner B.continuous)) (fun u => ?_)
    (K_sub t P htt (Submodule.starProjection_apply_mem _ x))
  have e : inner ℂ (t u) (B (t u)) = inner ℂ u (C u) := by
    have hsw : ∀ a b, inner ℂ (t a) b = inner ℂ a (t b) := fun a b => by
      conv_lhs => rw [← ht]
      exact ContinuousLinearMap.adjoint_inner_left t b a
    rw [hsw, ← hB]; rfl
  simp only [e]
  exact ((ContinuousLinearMap.nonneg_iff_isPositive C).mp hC).re_inner_nonneg_right u

/-- Weak resolution of the support projection by compressed sandwich solutions. -/
lemma resol {L : Type} (t P : E →L[ℂ] E) (ht : ContinuousLinearMap.adjoint t = t)
    (htt : t * t = P) (B C : L → E →L[ℂ] E)
    (hS : ∀ i, ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection).comp
          ((B i).comp ((LinearMap.range P.toLinearMap).topologicalClosure.starProjection)) = B i)
    (hB : ∀ i, t.comp ((B i).comp t) = C i) (hC : ∀ i, 0 ≤ C i)
    (hsum : ∀ y, HasSum (fun i => (inner ℂ y (C i y)).re) (inner ℂ y (P y)).re) (x : E) :
    HasSum (fun i => (inner ℂ x (B i x)).re)
      (inner ℂ x (((LinearMap.range P.toLinearMap).topologicalClosure.starProjection) x)).re := by
  set K := (LinearMap.range P.toLinearMap).topologicalClosure with hK
  set S := K.starProjection with hSdef
  have hBpos : ∀ i z, 0 ≤ (inner ℂ z (B i z)).re := fun i z =>
    pos_of_sandwich t P (B i) (C i) ht htt (hS i) (hB i) (hC i) z
  have hCpos : ∀ i u, 0 ≤ (inner ℂ u (C i u)).re := fun i u =>
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (hC i)).re_inner_nonneg_right u
  set TF : Finset L → E →L[ℂ] E := fun F => S - ∑ i ∈ F, B i with hTF
  have hSS : ∀ z, S (S z) = S z := fun z =>
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ z)
  have hTFS : ∀ F, S.comp ((TF F).comp S) = TF F := by
    intro F
    ext1 z
    simp only [hTF, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply, map_sub, map_sum, hSS]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    conv_rhs => rw [← hS i]
    rfl
  have hval : ∀ F z, (inner ℂ z (TF F z)).re =
      (inner ℂ z (S z)).re - ∑ i ∈ F, (inner ℂ z (B i z)).re := by
    intro F z
    simp only [hTF, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, inner_sub_right,
      inner_sum, Complex.sub_re, Complex.re_sum]
  have hSt : ∀ u, S (t u) = t u := fun u =>
    Submodule.starProjection_eq_self_iff.mpr (mem_K t P ht htt u)
  have htv : ∀ F u, (inner ℂ (t u) (TF F (t u))).re =
      (inner ℂ u (P u)).re - ∑ i ∈ F, (inner ℂ u (C i u)).re := by
    intro F u
    rw [hval, hSt]
    have hsw : ∀ a b, inner ℂ (t a) b = inner ℂ a (t b) := fun a b => by
      conv_lhs => rw [← ht]
      exact ContinuousLinearMap.adjoint_inner_left t b a
    congr 1
    · rw [hsw, ← htt]; rfl
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hsw, ← hB i]; rfl
  have hpos : ∀ F z, 0 ≤ (inner ℂ z (TF F z)).re := by
    intro F z
    rw [compress_form K (TF F) (hTFS F) z]
    refine cl_nonneg t (fun z => (inner ℂ z (TF F z)).re)
      (Complex.continuous_re.comp (continuous_id.inner (TF F).continuous)) (fun u => ?_)
      (K_sub t P htt (Submodule.starProjection_apply_mem _ z))
    show 0 ≤ (inner ℂ (t u) (TF F (t u))).re
    rw [htv]
    exact sub_nonneg.mpr (sum_le_hasSum F (fun i _ => hCpos i u) (hsum u))
  have hle : ∀ F z, (inner ℂ z (TF F z)).re ≤ ‖z‖ ^ 2 := by
    intro F z
    rw [hval]
    have h1 : 0 ≤ ∑ i ∈ F, (inner ℂ z (B i z)).re := Finset.sum_nonneg (fun i _ => hBpos i z)
    have h2 : (inner ℂ z (S z)).re ≤ ‖z‖ ^ 2 := by
      refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      rw [sq]
      exact mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ z) (norm_nonneg _)
    linarith
  have key : Tendsto (fun F : Finset L => (inner ℂ x (TF F x)).re) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hmem : S x ∈ closure (Set.range t) :=
      K_sub t P htt (Submodule.starProjection_apply_mem _ x)
    obtain ⟨b, ⟨y, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp hmem (min 1 (ε / 8)) (by positivity)
    have hd : ‖S x - t y‖ ^ 2 < ε / 8 := by
      rw [← dist_eq_norm]
      have h1 : dist (S x) (t y) < 1 := hb.trans_le (min_le_left _ _)
      have h2 : dist (S x) (t y) < ε / 8 := hb.trans_le (min_le_right _ _)
      nlinarith [dist_nonneg (x := S x) (y := t y)]
    have htl : Tendsto (fun F : Finset L =>
        (inner ℂ y (P y)).re - ∑ i ∈ F, (inner ℂ y (C i y)).re) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (inner ℂ y (P y)).re)).sub (hsum y)
    obtain ⟨F0, hF0⟩ := Filter.eventually_atTop.mp
      (htl.eventually (gt_mem_nhds (show (0:ℝ) < ε / 8 by positivity)))
    refine ⟨F0, fun F hF => ?_⟩
    have hty : (inner ℂ (t y) (TF F (t y))).re < ε / 8 := by rw [htv]; exact hF0 F hF
    have hpb := par_bound (TF F) (hpos F) (hle F) (S x) (t y)
    have hc := compress_form K (TF F) (hTFS F) x
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpos F x), hc]
    linarith
  have hm : Tendsto (fun F : Finset L => ∑ i ∈ F, (inner ℂ x (B i x)).re) atTop
      (𝓝 (inner ℂ x (S x)).re) := by
    have e : (fun F : Finset L => ∑ i ∈ F, (inner ℂ x (B i x)).re) =
        fun F => (inner ℂ x (S x)).re - (inner ℂ x (TF F x)).re := by
      funext F; rw [hval]; ring
    rw [e]
    simpa using (tendsto_const_nhds (x := (inner ℂ x (S x)).re)).sub key
  exact hm

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

/-- KEY for a channel image of a barycenter. -/
lemma chan_form_hasSum {I J L : Type} [Countable I] [Countable J] (Phi : Channel I J)
    (rho : L → State I) {pi : L → ℝ} (hpi : PositiveLaw pi) (sigma : State I)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b)
    (y : Hilbert J) :
    HasSum (fun j => pi j * (inner ℂ y (boundedOperator (Phi.val (rho j).coefficients) y)).re)
      (inner ℂ y (boundedOperator (Phi.val sigma.coefficients) y)).re := by
  have hpi0 : ∀ j, 0 ≤ pi j := fun j => (hpi.1 j).le
  have hs : sigma.coefficients = wm pi rho := hbar
  rw [hs, chan_wm Phi hpi0 hpi.2.summable rho]
  exact wm_form_hasSum' hpi0 hpi.2.summable (fun j => phiS Phi (rho j)) y


/-- N1b: Douglas resolution of the output support by the barycenter decomposition. -/
theorem n1b {I J L : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho : L → State I)
    (pi : L → ℝ) (sigma : State I) (hpi : PositiveLaw pi)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    ∃ B : L → (Hilbert J →L[ℂ] Hilbert J),
      (∀ i, (coefficientSupportProjection (Phi.val sigma.coefficients)).comp
          ((B i).comp (coefficientSupportProjection (Phi.val sigma.coefficients))) = B i) ∧
      (∀ i, (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients))).comp
          ((B i).comp (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)))) =
        (pi i : ℂ) • boundedOperator (Phi.val (rho i).coefficients)) ∧
      (∀ i, ContinuousLinearMap.adjoint (B i) = B i ∧ ∀ x, 0 ≤ (inner ℂ x (B i x)).re) ∧
      (∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
        (inner ℂ x (coefficientSupportProjection (Phi.val sigma.coefficients) x)).re) := by
  set P := boundedOperator (Phi.val sigma.coefficients) with hP
  set t := positiveSquareRoot P with htdef
  have hst := sqrt_state (phiS Phi sigma)
  have ht : ContinuousLinearMap.adjoint t = t := hst.1
  have htt : t * t = P := hst.2.1
  set C : L → Hilbert J →L[ℂ] Hilbert J :=
    fun i => (pi i : ℂ) • boundedOperator (Phi.val (rho i).coefficients) with hCdef
  have hC : ∀ i, 0 ≤ C i := fun i => by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    exact (bO_pos (phiS Phi (rho i))).smul_of_nonneg
      (by exact_mod_cast (hpi.1 i).le)
  have hCf : ∀ i y, (inner ℂ y (C i y)).re =
      pi i * (inner ℂ y (boundedOperator (Phi.val (rho i).coefficients) y)).re := by
    intro i y
    simp only [hCdef, ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]
  have hsum : ∀ y, HasSum (fun i => (inner ℂ y (C i y)).re) (inner ℂ y (P y)).re := by
    intro y
    simp only [hCf]
    exact chan_form_hasSum Phi rho hpi sigma hbar y
  have hle : ∀ i x, (inner ℂ x (C i x)).re ≤ (inner ℂ x (P x)).re := fun i x =>
    le_hasSum (hsum x) i (fun j _ =>
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (hC j)).re_inner_nonneg_right x)
  choose B hBS hBt hBa using fun i => douglas_sym t P (C i) ht htt (hC i) (hle i)
  exact ⟨B, hBS, hBt, fun i => ⟨hBa i, pos_of_sandwich t P (B i) (C i) ht htt (hBS i) (hBt i) (hC i)⟩,
    resol t P ht htt B C hBS hBt hC hsum⟩












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
theorem solution {I J L : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho : L → State I)
    (pi : L → ℝ) (sigma : State I) (hpi : PositiveLaw pi)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    ∃ B : L → (Hilbert J →L[ℂ] Hilbert J),
      (∀ i, (coefficientSupportProjection (Phi.val sigma.coefficients)).comp
          ((B i).comp (coefficientSupportProjection (Phi.val sigma.coefficients))) = B i) ∧
      (∀ i, (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients))).comp
          ((B i).comp (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)))) =
        (pi i : ℂ) • boundedOperator (Phi.val (rho i).coefficients)) ∧
      (∀ i, ContinuousLinearMap.adjoint (B i) = B i ∧ ∀ x, 0 ≤ (inner ℂ x (B i x)).re) ∧
      (∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
        (inner ℂ x (coefficientSupportProjection (Phi.val sigma.coefficients) x)).re) := by
  exact P45N1.n1b Phi rho pi sigma hpi hbar

end

end ChildRoot
