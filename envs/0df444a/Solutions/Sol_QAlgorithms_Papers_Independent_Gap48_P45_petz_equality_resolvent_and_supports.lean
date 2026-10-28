-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.petz_equality_resolvent_and_supports
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T02:53:39.081127+00:00
-- url     : https://prove2.me/submissions/8d8de28d-2306-43c0-b1c5-9c57ba767da3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false


section MainPart

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal ComplexConjugate Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace P45Petz

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsDensity IsTraceClassChannel traceSize NuclearExpansion tensorApply)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats)
open QAlgorithms.Papers.Independent.Frontier18.P18 (ReversibleOn boundedOperator operatorCoeff conjugateCoeff)

/-! Generic shortcut instances for bounded-operator coercions (speed: `AddMonoidHomClass (E →L[ℂ] F) E F` took 1-2 s). -/
section GSC2
variable {E F : Type} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SeminormedAddCommGroup F] [NormedSpace ℂ F]
instance (priority := 10000) gfc0 : FunLike (E →L[ℂ] F) E F := inferInstance
instance (priority := 10000) gfc1 : AddMonoidHomClass (E →L[ℂ] F) E F := inferInstance
instance (priority := 10000) gfc2 : ContinuousSemilinearMapClass (E →L[ℂ] F) (RingHom.id ℂ) E F := inferInstance
instance (priority := 10000) gfc3 : SemilinearMapClass (E →L[ℂ] F) (RingHom.id ℂ) E F := inferInstance
instance (priority := 10000) gfc4 : ContinuousMapClass (E →L[ℂ] F) E F := inferInstance
instance (priority := 10000) gfc5 : AddHomClass (E →L[ℂ] F) E F := inferInstance
instance (priority := 10000) gfc6 : ZeroHomClass (E →L[ℂ] F) E F := inferInstance
instance (priority := 10000) gfc7 : MulActionSemiHomClass (E →L[ℂ] F) (⇑(RingHom.id ℂ)) E F := inferInstance
end GSC2

/-! Generic shortcut instances on bounded operators (speed: TC search on `E →L[ℂ] E` is slow). -/
section GSC
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
instance (priority := 10000) gsc0 : Algebra ℝ (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc1 : Algebra ℂ (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc2 : StarRing (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc3 : PartialOrder (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc4 : StarOrderedRing (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc5 : NonUnitalRing (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc6 : Ring (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc7 : Module ℝ (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc8 : TopologicalSpace (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc9 : NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc10 : CStarAlgebra (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc11 : Module ℂ (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc12 : Semiring (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc13 : NormedRing (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc14 : NormedAlgebra ℂ (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc15 : CStarRing (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc16 : StarModule ℂ (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc17 : T2Space (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc18 : CompleteSpace (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc19 : NonUnitalSemiring (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc20 : IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc21 : SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc22 : AddMonoidWithOne (E →L[ℂ] E) := inferInstance
instance (priority := 10000) gsc23 : NormedAddCommGroup (E →L[ℂ] F) := inferInstance
instance (priority := 10000) gsc24 : Module ℂ (E →L[ℂ] F) := inferInstance
instance (priority := 10000) gsc25 : NormedSpace ℂ (E →L[ℂ] F) := inferInstance
instance (priority := 10000) gsc26 : AddCommGroup (E →L[ℂ] F) := inferInstance
instance (priority := 10000) gsc27 : TopologicalSpace (E →L[ℂ] F) := inferInstance
instance (priority := 10000) gsc28 : CompleteSpace (E →L[ℂ] F) := inferInstance
end GSC

/-! Shortcut instances for `Hilbert T = lp (fun _ => ℂ) 2` (speed: TC search on lp is slow). -/
instance (priority := 10000) hsc0 (T : Type) : NormedAddCommGroup (Hilbert T) := inferInstance
instance (priority := 10000) hsc1 (T : Type) : SeminormedAddCommGroup (Hilbert T) := inferInstance
instance (priority := 10000) hsc2 (T : Type) : PseudoMetricSpace (Hilbert T) := inferInstance
instance (priority := 10000) hsc3 (T : Type) : MetricSpace (Hilbert T) := inferInstance
instance (priority := 10000) hsc4 (T : Type) : TopologicalSpace (Hilbert T) := inferInstance
instance (priority := 10000) hsc5 (T : Type) : UniformSpace (Hilbert T) := inferInstance
instance (priority := 10000) hsc6 (T : Type) : AddCommGroup (Hilbert T) := inferInstance
instance (priority := 10000) hsc7 (T : Type) : AddCommMonoid (Hilbert T) := inferInstance
instance (priority := 10000) hsc8 (T : Type) : AddMonoid (Hilbert T) := inferInstance
instance (priority := 10000) hsc9 (T : Type) : AddZeroClass (Hilbert T) := inferInstance
instance (priority := 10000) hsc10 (T : Type) : AddGroup (Hilbert T) := inferInstance
instance (priority := 10000) hsc11 (T : Type) : Zero (Hilbert T) := inferInstance
instance (priority := 10000) hsc12 (T : Type) : Add (Hilbert T) := inferInstance
instance (priority := 10000) hsc13 (T : Type) : Neg (Hilbert T) := inferInstance
instance (priority := 10000) hsc14 (T : Type) : Sub (Hilbert T) := inferInstance
instance (priority := 10000) hsc15 (T : Type) : Norm (Hilbert T) := inferInstance
instance (priority := 10000) hsc16 (T : Type) : IsTopologicalAddGroup (Hilbert T) := inferInstance
instance (priority := 10000) hsc17 (T : Type) : ContinuousAdd (Hilbert T) := inferInstance
instance (priority := 10000) hsc18 (T : Type) : CompleteSpace (Hilbert T) := inferInstance
instance (priority := 10000) hsc19 (T : Type) : Module ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc20 (T : Type) : NormedSpace ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc21 (T : Type) : InnerProductSpace ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc22 (T : Type) : SMul ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc23 (T : Type) : ContinuousSMul ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc24 (T : Type) : ContinuousConstSMul ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc25 (T : Type) : DistribMulAction ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc26 (T : Type) : MulAction ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc27 (T : Type) : SMulWithZero ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc28 (T : Type) : MulActionWithZero ℂ (Hilbert T) := inferInstance
instance (priority := 10000) hsc29 (T : Type) : IsBoundedSMul ℂ (Hilbert T) := inferInstance



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
  have h' : HasSum (g ∘ Prod.swap) s := ((Equiv.prodComm β α).hasSum_iff (f := g)).mpr h
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

lemma summable_uncurry_of_swap {α β : Type} (g : α → β → ℝ) (hg0 : ∀ a b, 0 ≤ g a b)
    (hg1 : ∀ b, Summable (fun a => g a b)) (hg2 : Summable (fun b => ∑' a, g a b)) :
    Summable (Function.uncurry g) := by
  have hu : Summable (Function.uncurry (fun b a => g a b)) :=
    (summable_prod_of_nonneg (fun p => hg0 p.2 p.1)).2 ⟨hg1, hg2⟩
  have := ((Equiv.prodComm α β).summable_iff (f := Function.uncurry (fun b a => g a b))).mpr hu
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

/-! ## s4: positivity of trace pairings -/

/-! ## s4 U3: complete positivity pieces -/

lemma amp_mem {I : Type} {n : ℕ} (x : Fin n → Hilbert I) :
    Memℓp (fun p : I × Fin n => x p.2 p.1) 2 :=
  (memℓp_two_iff' _).mpr (hasSum_prod_fin (f := fun p : I × Fin n => ‖x p.2 p.1‖ ^ 2)
    (fun a => hasSum_normSq (x a))).summable

def amp {I : Type} {n : ℕ} (x : Fin n → Hilbert I) : Hilbert (I × Fin n) :=
  ⟨fun p => x p.2 p.1, amp_mem x⟩

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

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- A state is the sum of the rank-ones of the columns of its square root. -/
lemma dens_exp {T : Type} (rho : State T) (p q : T) :
    HasSum (fun k => (positiveSquareRoot (boundedOperator rho.coefficients) (bvec k)) p *
      star ((positiveSquareRoot (boundedOperator rho.coefficients) (bvec k)) q))
      (rho.coefficients p q) := by
  obtain ⟨hr, hrr, _⟩ := sqrt_state rho
  set r := positiveSquareRoot (boundedOperator rho.coefficients) with hrdef
  have hsa : IsSelfAdjoint r := (ContinuousLinearMap.isSelfAdjoint_iff' ).mpr hr
  have hpq : rho.coefficients p q = inner ℂ (r (bvec p)) (r (bvec q)) := by
    rw [← congrFun (congrFun (coeff_bO rho.density.1) p) q, ← hrr, operatorCoeff_apply,
      ← sa_swap hr, ← inner_bvec_left p]
    rfl
  rw [hpq]
  have h := lp.hasSum_inner (𝕜 := ℂ) (r (bvec p)) (r (bvec q))
  refine HasSum.congr_fun h (fun k => ?_)
  have e1 : (r (bvec k)) p = star ((r (bvec p)) k) := sa_coord hsa k p
  have e2 : (r (bvec k)) q = star ((r (bvec q)) k) := sa_coord hsa k q
  rw [e1, e2, star_star]
  simp [RCLike.inner_apply, mul_comm]

lemma slice_mem {J A : Type} (x : Hilbert (J × A)) (a : A) :
    Memℓp (fun j : J => x (j, a)) 2 :=
  (memℓp_two_iff' _).mpr ((hasSum_normSq x).summable.comp_injective
    (f := fun p : J × A => ‖x p‖ ^ 2) (i := fun j : J => (j, a))
    (fun j j' h => (Prod.mk.inj h).1))

def slice {J A : Type} (x : Hilbert (J × A)) (a : A) : Hilbert J := ⟨fun j => x (j, a), slice_mem x a⟩

lemma slice_norm {J A : Type} (x : Hilbert (J × A)) (a : A) : ‖slice x a‖ ≤ ‖x‖ := by
  have h1 := (hasSum_normSq (slice x a)).tsum_eq
  have h2 := (hasSum_normSq x).tsum_eq
  have hle : ∑' j, ‖(slice x a) j‖ ^ 2 ≤ ∑' p, ‖x p‖ ^ 2 :=
    tsum_comp_le_tsum_of_inj (f := fun p : J × A => ‖x p‖ ^ 2) (hasSum_normSq x).summable
      (fun _ => sq_nonneg _) (i := fun j : J => (j, a)) (fun j j' h => (Prod.mk.inj h).1)
  rw [h1, h2] at hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- U3e core: the pairing of a block of a state with a bounded B, via square-root columns. -/
lemma block_pair {J A : Type} (rho : State (J × A)) (a b : A) (B : Hilbert J →L[ℂ] Hilbert J) :
    HasSum (fun k => inner ℂ (slice (positiveSquareRoot (boundedOperator rho.coefficients) (bvec k)) b)
        (B (slice (positiveSquareRoot (boundedOperator rho.coefficients) (bvec k)) a)))
      (boundedTracePair (fun j j' => rho.coefficients (j, a) (j', b)) B) := by
  obtain ⟨_, _, hsum⟩ := sqrt_state rho
  set r := positiveSquareRoot (boundedOperator rho.coefficients) with hrdef
  refine pair_gen B (fun k => slice (r (bvec k)) a) (fun k => slice (r (bvec k)) b) ?_
    (fun i j => dens_exp rho (i, a) (j, b))
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum.summable
  rw [sq]
  exact mul_le_mul (slice_norm _ _) (slice_norm _ _) (norm_nonneg _) (norm_nonneg _)

/-! ## s5: U3b, positivity of the supported dual on rank-one families -/

/-! ## s6: U4 normality of the Petz dual -/

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

end P45Petz


end

end MainPart

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

lemma summable_prod_of_fibers_nonneg' {f : κ × ι → ℝ} (hf : ∀ p, 0 ≤ f p) {g : ι → ℝ}
    (hg : ∀ i, HasSum (fun j => f (j, i)) (g i)) (hgs : Summable g) : Summable f :=
  (hasSum_prod_of_fibers_nonneg' hf hg hgs).summable

lemma hasSum_prod_of_fibers' {f : κ × ι → ℝ} (hf : Summable f) {g : ι → ℝ}
    (hg : ∀ i, HasSum (fun j => f (j, i)) (g i)) : HasSum f (∑' i, g i) := by
  have hf' : Summable (fun q : ι × κ => f (q.2, q.1)) :=
    ((Equiv.prodComm ι κ).summable_iff (f := f)).mpr hf
  have h := hasSum_prod_of_fibers hf' hg
  exact ((Equiv.prodComm ι κ).hasSum_iff (f := f)).mp h

/-- Termwise identity: d |w - (r/d) c|^2 = d |w|^2 - 2 r Re(conj c * w) + |c|^2 r^2 / d. -/
lemma term_id (c w : ℂ) {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 < t) :
    (s + t * r) * ‖w - ((r / (s + t * r) : ℝ) : ℂ) * c‖ ^ 2 =
      s * ‖w‖ ^ 2 + t * (r * ‖w‖ ^ 2) - 2 * (r * ((starRingEnd ℂ) c * w).re)
        + ‖c‖ ^ 2 * r ^ 2 / (s + t * r) := by
  rcases (add_nonneg hs (mul_nonneg ht.le hr)).lt_or_eq with hd | hd
  · simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  · have htr : t * r = 0 := by linarith [mul_nonneg ht.le hr]
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp htr with h | h
      · exact absurd h ht.ne'
      · exact h
    have hs0 : s = 0 := by linarith
    subst hr0; subst hs0
    simp

theorem parseval_id (e : HilbertBasis ι ℂ E) (f : HilbertBasis κ ℂ E)
    (r : ι → ℝ) (s : κ → ℝ) (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j)
    (hrs : Summable r) (hss : Summable s) {t : ℝ} (ht : 0 < t) (W : E →L[ℂ] E) :
    HasSum (fun p : κ × ι => (s p.1 + t * r p.2) *
        ‖⟪f p.1, W (e p.2)⟫_ℂ - ((r p.2 / (s p.1 + t * r p.2) : ℝ) : ℂ) * ⟪f p.1, e p.2⟫_ℂ‖ ^ 2)
      ((∑' p : κ × ι, ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 / (s p.1 + t * r p.2))
        - 2 * (∑' i, r i * (⟪e i, W (e i)⟫_ℂ).re)
        + ∑' j, s j * ‖(ContinuousLinearMap.adjoint W) (f j)‖ ^ 2
        + t * ∑' i, r i * ‖W (e i)‖ ^ 2) := by
  set A := ContinuousLinearMap.adjoint W
  -- T1: s_j |w_ji|^2, fibres over j
  have hw1 : ∀ j i, ‖⟪f j, W (e i)⟫_ℂ‖ = ‖⟪e i, A (f j)⟫_ℂ‖ := by
    intro j i
    rw [← ContinuousLinearMap.adjoint_inner_left W (e i) (f j), norm_inner_symm]
  have hA : ‖A‖ = ‖W‖ := LinearIsometryEquiv.norm_map _ W
  have hT1 : HasSum (fun p : κ × ι => s p.1 * ‖⟪f p.1, W (e p.2)⟫_ℂ‖ ^ 2)
      (∑' j, s j * ‖A (f j)‖ ^ 2) := by
    refine hasSum_prod_of_fibers_nonneg (fun p => mul_nonneg (hs _) (sq_nonneg _))
      (fun j => ?_) ?_
    · simp only [hw1]
      exact (hb_norm_sq e (A (f j))).mul_left (s j)
    · refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hs j) (sq_nonneg _)) (fun j => ?_)
        (hss.mul_right (‖W‖ ^ 2))
      refine mul_le_mul_of_nonneg_left ?_ (hs j)
      have h1 : ‖A (f j)‖ ≤ ‖W‖ := by
        calc ‖A (f j)‖ ≤ ‖A‖ * ‖f j‖ := A.le_opNorm _
          _ = ‖W‖ := by rw [hA, f.orthonormal.1 j, mul_one]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  -- T2: r_i |w_ji|^2, fibres over i
  have hR2 : Summable (fun i => r i * ‖W (e i)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hr i) (sq_nonneg _)) (fun i => ?_)
      (hrs.mul_right (‖W‖ ^ 2))
    refine mul_le_mul_of_nonneg_left ?_ (hr i)
    have h1 : ‖W (e i)‖ ≤ ‖W‖ := by
      calc ‖W (e i)‖ ≤ ‖W‖ * ‖e i‖ := W.le_opNorm _
        _ = ‖W‖ := by rw [e.orthonormal.1 i, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hT2 : HasSum (fun p : κ × ι => r p.2 * ‖⟪f p.1, W (e p.2)⟫_ℂ‖ ^ 2)
      (∑' i, r i * ‖W (e i)‖ ^ 2) :=
    hasSum_prod_of_fibers_nonneg' (fun p => mul_nonneg (hr _) (sq_nonneg _))
      (fun i => (hb_norm_sq f (W (e i))).mul_left (r i)) hR2
  -- T3: cross term
  have hc1 : ∀ i, HasSum (fun j => ‖⟪f j, e i⟫_ℂ‖ ^ 2) 1 := by
    intro i
    have := hb_norm_sq f (e i)
    rwa [e.orthonormal.1 i, one_pow] at this
  have hT3 : HasSum (fun p : κ × ι => r p.2 * ((starRingEnd ℂ) ⟪f p.1, e p.2⟫_ℂ *
        ⟪f p.1, W (e p.2)⟫_ℂ).re) (∑' i, r i * (⟪e i, W (e i)⟫_ℂ).re) := by
    have hfib : ∀ i, HasSum (fun j => r i * ((starRingEnd ℂ) ⟪f j, e i⟫_ℂ *
        ⟪f j, W (e i)⟫_ℂ).re) (r i * (⟪e i, W (e i)⟫_ℂ).re) := by
      intro i
      have h := f.hasSum_inner_mul_inner (e i) (W (e i))
      have h' := (Complex.reCLM.hasSum h).mul_left (r i)
      refine h'.congr_fun (fun j => ?_)
      simp [inner_conj_symm]
    refine hasSum_prod_of_fibers' ?_ hfib
    -- domination by r_i (|c|^2 + |w|^2) / 2
    have hbd : Summable (fun p : κ × ι =>
        r p.2 * (‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 + ‖⟪f p.1, W (e p.2)⟫_ℂ‖ ^ 2)) := by
      refine summable_prod_of_fibers_nonneg' (fun p => mul_nonneg (hr _)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
        (fun i => ((hc1 i).add (hb_norm_sq f (W (e i)))).mul_left (r i)) ?_
      exact (hrs.add hR2).congr (fun i => by ring)
    refine Summable.of_norm_bounded hbd (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr _)]
    refine mul_le_mul_of_nonneg_left ?_ (hr _)
    calc |((starRingEnd ℂ) ⟪f p.1, e p.2⟫_ℂ * ⟪f p.1, W (e p.2)⟫_ℂ).re|
        ≤ ‖(starRingEnd ℂ) ⟪f p.1, e p.2⟫_ℂ * ⟪f p.1, W (e p.2)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ = ‖⟪f p.1, e p.2⟫_ℂ‖ * ‖⟪f p.1, W (e p.2)⟫_ℂ‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 + ‖⟪f p.1, W (e p.2)⟫_ℂ‖ ^ 2 := by
          nlinarith [sq_nonneg (‖⟪f p.1, e p.2⟫_ℂ‖ - ‖⟪f p.1, W (e p.2)⟫_ℂ‖),
            norm_nonneg ⟪f p.1, e p.2⟫_ℂ, norm_nonneg ⟪f p.1, W (e p.2)⟫_ℂ]
  -- T4: the explicit Q
  have hT4 : Summable (fun p : κ × ι => ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 /
      (s p.1 + t * r p.2)) := by
    have hb : Summable (fun p : κ × ι => ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * (r p.2 / t)) :=
      summable_prod_of_fibers_nonneg' (fun p => mul_nonneg (sq_nonneg _)
        (div_nonneg (hr _) ht.le)) (fun i => by simpa using (hc1 i).mul_right (r i / t))
        (hrs.div_const t)
    refine Summable.of_nonneg_of_le (fun p => div_nonneg (mul_nonneg (sq_nonneg _)
      (sq_nonneg _)) (add_nonneg (hs _) (mul_nonneg ht.le (hr _)))) (fun p => ?_) hb
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rcases (hr p.2).lt_or_eq with h | h
    · rw [div_le_div_iff₀ (by nlinarith [hs p.1]) ht]
      nlinarith [hs p.1, hr p.2]
    · rw [← h]; simp
  have hsum := (((hT4.hasSum.sub (hT3.mul_left 2)).add hT1).add (hT2.mul_left t))
  refine hsum.congr_fun (fun p => ?_)
  rw [term_id _ _ (hr p.2) (hs p.1) ht]
  ring

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

/-- The explicit optimum Q_t = Sum |c_ji|^2 r_i^2 / (s_j + t r_i). -/
def Qv : ℝ := ∑' p : κ × ι, ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 / (s p.1 + t * r p.2)

/-- The optimal coefficients y_ji = c_ji r_i / (s_j + t r_i). -/
def yc (p : κ × ι) : ℂ := ((r p.2 / (s p.1 + t * r p.2) : ℝ) : ℂ) * ⟪f p.1, e p.2⟫_ℂ

/-- Finite-rank truncation of the optimiser. -/
def truncOp (F : Finset (κ × ι)) : E →L[ℂ] E :=
  ∑ p ∈ F, yc e f r s t p • InnerProductSpace.rankOne ℂ (f p.1) (e p.2)

lemma truncOp_coeff (F : Finset (κ × ι)) (j : κ) (i : ι) :
    ⟪f j, truncOp e f r s t F (e i)⟫_ℂ = if (j, i) ∈ F then yc e f r s t (j, i) else 0 := by
  simp only [truncOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply, inner_sum, inner_smul_right]
  rw [Finset.sum_congr rfl (g := fun p => if p = (j, i) then yc e f r s t (j, i) else 0),
    Finset.sum_ite_eq']
  rintro ⟨a, b⟩ _
  rw [orthonormal_iff_ite.mp e.orthonormal b i, orthonormal_iff_ite.mp f.orthonormal j a]
  by_cases h1 : j = a <;> by_cases h2 : b = i
  · subst h1; subst h2; simp
  · simp [h1, h2, Prod.ext_iff]
  · simp [h1, h2, Prod.ext_iff, Ne.symm h1]
  · simp [h1, h2, Prod.ext_iff, Ne.symm h1]

variable {r s t}

lemma parseval_val (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) (hrs : Summable r) (hss : Summable s)
    (ht : 0 < t) (W : E →L[ℂ] E) :
    HasSum (fun p : κ × ι => (s p.1 + t * r p.2) * ‖⟪f p.1, W (e p.2)⟫_ℂ - yc e f r s t p‖ ^ 2)
      (Qv e f r s t - val e f r s t W) := by
  have h := parseval_id e f r s hr hs hrs hss ht W
  have hv : Qv e f r s t - val e f r s t W = (∑' p : κ × ι, ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 /
        (s p.1 + t * r p.2))
        - 2 * (∑' i, r i * (⟪e i, W (e i)⟫_ℂ).re)
        + ∑' j, s j * ‖(ContinuousLinearMap.adjoint W) (f j)‖ ^ 2
        + t * ∑' i, r i * ‖W (e i)‖ ^ 2 := by
    unfold Qv val
    ring
  rw [hv]
  exact h

theorem val_le (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) (hrs : Summable r) (hss : Summable s)
    (ht : 0 < t) (W : E →L[ℂ] E) : val e f r s t W ≤ Qv e f r s t := by
  have h := parseval_val e f hr hs hrs hss ht W
  have := h.nonneg (fun p => mul_nonneg (add_nonneg (hs _) (mul_nonneg ht.le (hr _)))
    (sq_nonneg _))
  linarith

lemma d_ysq (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) (ht : 0 < t) (p : κ × ι) :
    (s p.1 + t * r p.2) * ‖yc e f r s t p‖ ^ 2 =
      ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 / (s p.1 + t * r p.2) := by
  have hd0 := add_nonneg (hs p.1) (mul_nonneg ht.le (hr p.2))
  rcases hd0.lt_or_eq with hd | hd
  · simp only [yc, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  · rw [← hd]; simp

theorem trunc_resid (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) (hrs : Summable r)
    (hss : Summable s) (ht : 0 < t) (F : Finset (κ × ι)) :
    HasSum (fun p : κ × ι => if p ∈ F then 0 else
        ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 / (s p.1 + t * r p.2))
      (Qv e f r s t - val e f r s t (truncOp e f r s t F)) := by
  refine (parseval_val e f hr hs hrs hss ht _).congr_fun (fun p => ?_)
  rw [truncOp_coeff]
  by_cases hp : p ∈ F
  · simp [hp]
  · simp only [hp, if_false, zero_sub, norm_neg]
    exact (d_ysq e f hr hs ht p).symm

theorem val_trunc_tendsto (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) (hrs : Summable r)
    (hss : Summable s) (ht : 0 < t) :
    Filter.Tendsto (fun F : Finset (κ × ι) => val e f r s t (truncOp e f r s t F))
      Filter.atTop (nhds (Qv e f r s t)) := by
  set g : κ × ι → ℝ := fun p => ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 / (s p.1 + t * r p.2)
  have hQ : HasSum g (Qv e f r s t) := by
    have h0 := trunc_resid e f hr hs hrs hss ht ∅
    have hv0 : truncOp e f r s t ∅ = 0 := by simp [truncOp]
    have hval0 : val e f r s t 0 = 0 := by simp [val]
    rw [hv0, hval0, sub_zero] at h0
    exact h0.congr_fun (fun p => by simp [g])
  have hlim := tendsto_tsum_compl_atTop_zero g
  have heq : ∀ F : Finset (κ × ι), (∑' p : {x // x ∉ F}, g p) =
      Qv e f r s t - val e f r s t (truncOp e f r s t F) := by
    intro F
    have h1 : (∑' p : {x // x ∉ F}, g p) =
        ∑' p, ({x | x ∉ F} : Set (κ × ι)).indicator g p :=
      tsum_subtype ({x | x ∉ F} : Set (κ × ι)) g
    rw [h1, ← (trunc_resid e f hr hs hrs hss ht F).tsum_eq]
    refine tsum_congr (fun p => ?_)
    by_cases hp : p ∈ F <;> simp [hp, Set.indicator, g]
  have : Filter.Tendsto (fun F : Finset (κ × ι) =>
      Qv e f r s t - (Qv e f r s t - val e f r s t (truncOp e f r s t F))) Filter.atTop
      (nhds (Qv e f r s t - 0)) := tendsto_const_nhds.sub (by simpa only [heq] using hlim)
  simpa using this

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

/-- Tr(rho W W*) = Sum r_i ‖W* e_i‖^2 (as a real number, the pairing being real). -/
theorem pair_eigen_sq {T ι : Type} (rho : State T) (e : HilbertBasis ι ℂ (Hilbert T)) (r : ι → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (W : Hilbert T →L[ℂ] Hilbert T) :
    HasSum (fun i => r i * ‖W (e i)‖ ^ 2)
      (boundedTracePair rho.coefficients ((ContinuousLinearMap.adjoint W).comp W)).re := by
  have h := Complex.hasSum_re (pair_eigen rho e r hr0 hr1 hev ((ContinuousLinearMap.adjoint W).comp W))
  convert h using 1
  funext i
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

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

lemma pair_one {T : Type} {X : Matrix T T ℂ} (hX : IsTraceClass X) :
    boundedTracePair X (ContinuousLinearMap.id ℂ (Hilbert T)) = ∑' i, X i i := by
  unfold boundedTracePair
  rw [ContinuousLinearMap.id_comp, coeff_bO hX]

/-- Trace preservation in the Heisenberg picture: Phi*(1) = 1. -/
theorem dual_one (Phi : Channel I J) :
    channelDual Phi.val (ContinuousLinearMap.id ℂ (Hilbert J)) = ContinuousLinearMap.id ℂ (Hilbert I) := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [channelDual_inner]
  unfold dF dG
  obtain ⟨t, h1, h2⟩ := chan_trace Phi (tc_rk y x)
  rw [pair_one (Phi.property.1 _ (tc_rk y x)), h2.tsum_eq, ← h1.tsum_eq, ContinuousLinearMap.id_apply,
    inner_eq_tsum']
  refine tsum_congr (fun i => ?_)
  rw [coeff_rk, mul_comm]

end Dual

end P45C4B

end

end C4Bridge


/-! K-b scalar identity (s13): Int_0^inf (r-s)^2/((s+tr)(1+t)^2) dt = r log r - r log s + s - r (s > 0, r ≥ 0). -/

open MeasureTheory Set Filter Topology

namespace P45KB

/-- Antiderivative of the K-b kernel. -/
noncomputable def kbF (r s t : ℝ) : ℝ := r * Real.log (s + t * r) - r * Real.log (1 + t) - (s - r) / (1 + t)

/-- The K-b kernel. -/
noncomputable def kbK (r s t : ℝ) : ℝ := (r - s) ^ 2 / ((s + t * r) * (1 + t) ^ 2)

lemma kbK_nonneg {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 < s) (ht : 0 ≤ t) : 0 ≤ kbK r s t := by
  unfold kbK
  have h1 : 0 < s + t * r := by nlinarith [mul_nonneg ht hr]
  positivity

lemma kbF_deriv {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 < s) (ht : 0 ≤ t) :
    HasDerivAt (kbF r s) (kbK r s t) t := by
  have h1 : 0 < s + t * r := by nlinarith [mul_nonneg ht hr]
  have h2 : 0 < 1 + t := by linarith
  have d1 : HasDerivAt (fun x => s + x * r) r t := by
    simpa using ((hasDerivAt_id t).mul_const r).const_add s
  have d2 : HasDerivAt (fun x => 1 + x) 1 t := by simpa using (hasDerivAt_id t).const_add 1
  have dl1 := (d1.log h1.ne').const_mul r
  have dl2 := (d2.log h2.ne').const_mul r
  have dq := (d2.inv h2.ne').const_mul (s - r)
  have hall := (dl1.sub dl2).sub dq
  have hfun : kbF r s = (((fun y => r * Real.log (s + y * r)) - fun y => r * Real.log (1 + y)) -
      fun y => (s - r) * (fun x => 1 + x)⁻¹ y) := by
    funext x; simp only [kbF, Pi.sub_apply, Pi.inv_apply, div_eq_mul_inv]
  have hval : kbK r s t =
      r * (r / (s + t * r)) - r * (1 / (1 + t)) - (s - r) * (-1 / (1 + t) ^ 2) := by
    unfold kbK; field_simp; ring
  rw [hfun, hval]; exact hall

lemma kbF_tendsto {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    Tendsto (kbF r s) atTop (𝓝 (r * Real.log r)) := by
  have hq : Tendsto (fun t : ℝ => (s - r) / (1 + t)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_id)
  rcases hr.lt_or_eq with hr' | hr'
  · have hratio : Tendsto (fun t : ℝ => (s + t * r) / (1 + t)) atTop (𝓝 r) := by
      have h1 : Tendsto (fun t : ℝ => (s - r) / (1 + t) + r) atTop (𝓝 (0 + r)) := hq.add_const r
      rw [zero_add] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      field_simp
      ring
    have hlog := ((Real.continuousAt_log hr'.ne').tendsto.comp hratio).const_mul r
    have h3 := hlog.sub hq
    rw [sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h1 : 0 < s + t * r := by positivity
    have h2 : 0 < 1 + t := by linarith
    simp only [Function.comp, kbF]
    rw [Real.log_div h1.ne' h2.ne']
    ring
  · subst hr'
    have h3 := hq.neg
    rw [neg_zero] at h3
    simp only [zero_mul, mul_zero, Real.log_zero]
    refine h3.congr' (Eventually.of_forall fun t => ?_)
    simp [kbF, neg_div]

/-- K-b scalar identity. -/
theorem kb_scalar {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), kbK r s t = r * Real.log r - r * Real.log s + s - r := by
  have hc : ContinuousWithinAt (kbF r s) (Ici 0) 0 :=
    (kbF_deriv hr hs le_rfl).continuousAt.continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_nonneg hc (fun t ht => kbF_deriv hr hs (le_of_lt ht))
    (fun t ht => kbK_nonneg hr hs (le_of_lt ht)) (kbF_tendsto hr hs)
  rw [h]
  simp [kbF]
  ring

lemma kbK_integrable {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) : IntegrableOn (kbK r s) (Ioi 0) := by
  have hc : ContinuousWithinAt (kbF r s) (Ici 0) 0 :=
    (kbF_deriv hr hs le_rfl).continuousAt.continuousWithinAt
  exact integrableOn_Ioi_deriv_of_nonneg hc (fun t ht => kbF_deriv hr hs (le_of_lt ht))
    (fun t ht => kbK_nonneg hr hs (le_of_lt ht)) (kbF_tendsto hr hs)

/-- K-b scalar identity, lintegral form. -/
theorem kb_scalar_lint {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (kbK r s t) =
      ENNReal.ofReal (r * Real.log r - r * Real.log s + s - r) := by
  rw [← kb_scalar hr hs, ofReal_integral_eq_lintegral_ofReal (kbK_integrable hr hs)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact kbK_nonneg hr hs (le_of_lt ht)

end P45KB


/-! ## C4 K-c rest (s13): 2-block lemma, *-preservation, Kadison-Schwarz, monotonicity of val.
Iteration file: imports the laptop-built olean of 0d372677_c4b.lean (module P45S.C4b). -/
section C4cPart

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace P45C4C

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)
open P45Petz P45C4 P45C4B
open scoped InnerProductSpace

variable {I J : Type}

/-- 2-block lemma, unit case: the 2x2 block output of a channel as a sum of column pairs. -/
lemma blk2_unit (Phi : Channel I J) (v : Fin 2 → Hilbert I) (hv : ‖amp v‖ = 1) :
    ∃ (K : Type) (w : Fin 2 → K → Hilbert J), (∀ a, Summable (fun k => ‖w a k‖ ^ 2)) ∧
      ∀ a b (B : Hilbert J →L[ℂ] Hilbert J),
        HasSum (fun k => ⟪w b k, B (w a k)⟫_ℂ) ⟪v b, channelDual Phi.val B (v a)⟫_ℂ := by
  have hρ := isDensity_rk (amp v) hv
  set M : State (J × Fin 2) := ⟨_, Phi.property.2.2.2 2 ⟨_, hρ⟩⟩ with hM
  obtain ⟨_, _, hsum⟩ := sqrt_state M
  set r := positiveSquareRoot (boundedOperator M.coefficients) with hr
  refine ⟨J × Fin 2, fun a k => slice (r (bvec k)) a, fun a => ?_, fun a b B => ?_⟩
  · exact Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => pow_le_pow_left₀ (norm_nonneg _) (slice_norm _ _) 2) hsum.summable
  · have h := block_pair M a b B
    have hin : (fun i i' => operatorCoeff (rk (amp v) (amp v)) (i, a) (i', b)) =
        operatorCoeff (rk (v a) (v b)) := by
      funext i i'; rw [coeff_rk, coeff_rk]; rfl
    have hblk : (fun j j' => M.coefficients (j, a) (j', b)) =
        Phi.val (operatorCoeff (rk (v a) (v b))) := by
      funext j j'
      change Phi.val (fun i i' => operatorCoeff (rk (amp v) (amp v)) (i, a) (i', b)) j j' = _
      rw [hin]
    rw [hblk] at h
    rw [channelDual_inner]
    exact h

/-- 2-block lemma: for v_0, v_1 there are square-summable columns w_0, w_1 with
<v_b, Phi*(B) v_a> = Sum_k <w_b k, B w_a k> for every bounded B. -/
lemma blk2 (Phi : Channel I J) (v : Fin 2 → Hilbert I) :
    ∃ (K : Type) (w : Fin 2 → K → Hilbert J), (∀ a, Summable (fun k => ‖w a k‖ ^ 2)) ∧
      ∀ a b (B : Hilbert J →L[ℂ] Hilbert J),
        HasSum (fun k => ⟪w b k, B (w a k)⟫_ℂ) ⟪v b, channelDual Phi.val B (v a)⟫_ℂ := by
  set N := ‖amp v‖ with hN
  rcases (norm_nonneg (amp v)).lt_or_eq with hpos | hzero
  · set k : ℂ := ((N⁻¹ : ℝ) : ℂ) with hk
    set v' : Fin 2 → Hilbert I := fun a => k • v a with hv'
    have hamp : amp v' = k • amp v := lp.ext (funext fun p => rfl)
    have hn1 : ‖amp v'‖ = 1 := by
      rw [hamp, norm_smul, hk, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos), ← hN, inv_mul_cancel₀ hpos.ne']
    obtain ⟨K, w, hw, hw2⟩ := blk2_unit Phi v' hn1
    have hv : ∀ a, v a = (N : ℂ) • v' a := fun a => by
      simp only [hv', smul_smul, hk, ← Complex.ofReal_mul]
      rw [mul_inv_cancel₀ (show N ≠ 0 from hpos.ne'), Complex.ofReal_one, one_smul]
    refine ⟨K, fun a i => (N : ℂ) • w a i, fun a => ?_, fun a b B => ?_⟩
    · refine ((hw a).mul_left (N ^ 2)).congr (fun i => ?_)
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, mul_pow]
    · have h := (hw2 a b B).mul_left ((N : ℂ) * N)
      have e1 : (fun i => ⟪(N : ℂ) • w b i, B ((N : ℂ) • w a i)⟫_ℂ) =
          fun i => (N : ℂ) * N * ⟪w b i, B (w a i)⟫_ℂ := by
        funext i; rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]; ring
      have e2 : ⟪v b, channelDual Phi.val B (v a)⟫_ℂ =
          (N : ℂ) * N * ⟪v' b, channelDual Phi.val B (v' a)⟫_ℂ := by
        rw [hv a, hv b, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]; ring
      show HasSum (fun i => ⟪(N : ℂ) • w b i, B ((N : ℂ) • w a i)⟫_ℂ) _
      rw [e1, e2]; exact h
  · have hz : amp v = 0 := norm_eq_zero.mp hzero.symm
    have h0 : ∀ a, v a = 0 := fun a => lp.ext (funext fun i => by
      have := congrArg (fun z : Hilbert (I × Fin 2) => z (i, a)) hz
      simp only [lp.coeFn_zero, Pi.zero_apply] at this ⊢
      exact this)
    refine ⟨Unit, fun _ _ => 0, fun a => by simp, fun a b B => by simp [h0]⟩

/-- *-preservation of the dual: Phi*(W)† = Phi*(W†). -/
theorem dual_adj (Phi : Channel I J) (W : Hilbert J →L[ℂ] Hilbert J) :
    ContinuousLinearMap.adjoint (channelDual Phi.val W) =
      channelDual Phi.val (ContinuousLinearMap.adjoint W) := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  obtain ⟨K, w, hw, hw2⟩ := blk2 Phi ![x, y]
  have h1 := hw2 1 0 (ContinuousLinearMap.adjoint W)
  have h2 := hw2 0 1 W
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1 h2
  have h3 : HasSum (fun k => ⟪w 0 k, ContinuousLinearMap.adjoint W (w 1 k)⟫_ℂ)
      (star ⟪y, channelDual Phi.val W x⟫_ℂ) := by
    convert h2.star using 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm]
    rfl
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm]
  exact h3.unique h1

/-- Kadison-Schwarz, vector form: ‖Phi*(A) x‖^2 ≤ Re <x, Phi*(A†A) x>. -/
theorem ks_vec (Phi : Channel I J) (A : Hilbert J →L[ℂ] Hilbert J) (x : Hilbert I) :
    ‖channelDual Phi.val A x‖ ^ 2 ≤
      (⟪x, channelDual Phi.val ((ContinuousLinearMap.adjoint A).comp A) x⟫_ℂ).re := by
  set y := channelDual Phi.val A x with hy
  obtain ⟨K, w, hw, hw2⟩ := blk2 Phi ![x, y]
  have h00 := hw2 0 0 ((ContinuousLinearMap.adjoint A).comp A)
  have h01 := hw2 0 1 A
  have h11 := hw2 1 1 (ContinuousLinearMap.id ℂ _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h00 h01 h11
  rw [dual_one, ContinuousLinearMap.id_apply] at h11
  have hs := ((Complex.hasSum_re h00).sub ((Complex.hasSum_re h01).mul_left 2)).add
    (Complex.hasSum_re h11)
  have hnn := hs.nonneg (fun k => by
    have e1 : (⟪w 0 k, ((ContinuousLinearMap.adjoint A).comp A) (w 0 k)⟫_ℂ).re =
        ‖A (w 0 k)‖ ^ 2 := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        ← RCLike.re_to_complex, inner_self_eq_norm_sq]
    have e2 : (⟪w 1 k, (ContinuousLinearMap.id ℂ (Hilbert J)) (w 1 k)⟫_ℂ).re = ‖w 1 k‖ ^ 2 := by
      rw [ContinuousLinearMap.id_apply, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
    have e3 : (⟪w 1 k, A (w 0 k)⟫_ℂ).re = RCLike.re ⟪A (w 0 k), w 1 k⟫_ℂ := by
      rw [← inner_re_symm, RCLike.re_to_complex]
    have e4 := @norm_sub_sq ℂ _ _ _ _ (A (w 0 k)) (w 1 k)
    simp only [Pi.sub_apply, Pi.add_apply, e1, e2, e3]
    nlinarith [sq_nonneg ‖A (w 0 k) - w 1 k‖])
  have hyy : (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 := by
    rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
  rw [hyy] at hnn
  linarith

/-- Kadison-Schwarz, trace form: Tr(sigma Phi*(A)† Phi*(A)) ≤ Tr(Phi(sigma) A† A). -/
theorem ks_trace (Phi : Channel I J) (sigma : State I) (A : Hilbert J →L[ℂ] Hilbert J) :
    (boundedTracePair sigma.coefficients ((ContinuousLinearMap.adjoint (channelDual Phi.val A)).comp
        (channelDual Phi.val A))).re ≤
      (boundedTracePair (Phi.val sigma.coefficients) ((ContinuousLinearMap.adjoint A).comp A)).re := by
  obtain ⟨ι, e, r, hr0, hr1, hev⟩ := state_eigen sigma
  have h1 := pair_eigen_sq sigma e r hr0 hr1.summable hev (channelDual Phi.val A)
  have h2 := Complex.hasSum_re (pair_eigen sigma e r hr0 hr1.summable hev
    (channelDual Phi.val ((ContinuousLinearMap.adjoint A).comp A)))
  rw [← dual_pair Phi _ _ sigma.density.1]
  refine hasSum_le (fun i => ?_) h1 h2
  rw [Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left (ks_vec Phi A (e i)) (hr0 i)

/-- val (eigen coordinates) in trace form. -/
lemma val_tr {T ι κ : Type} (rho sigma : State T) (e : HilbertBasis ι ℂ (Hilbert T))
    (f : HilbertBasis κ ℂ (Hilbert T)) (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (t : ℝ) (W : Hilbert T →L[ℂ] Hilbert T) :
    val e f r s t W = 2 * (boundedTracePair rho.coefficients W).re
      - (boundedTracePair sigma.coefficients ((ContinuousLinearMap.adjoint
          (ContinuousLinearMap.adjoint W)).comp (ContinuousLinearMap.adjoint W))).re
      - t * (boundedTracePair rho.coefficients ((ContinuousLinearMap.adjoint W).comp W)).re := by
  have h1 := Complex.hasSum_re (pair_eigen rho e r hr0 hr1 hev W)
  have h2 := pair_eigen_sq sigma f s hs0 hs1 hfv (ContinuousLinearMap.adjoint W)
  have h3 := pair_eigen_sq rho e r hr0 hr1 hev W
  simp only [Complex.re_ofReal_mul] at h1
  unfold val
  rw [h1.tsum_eq, h2.tsum_eq, h3.tsum_eq]

/-- K-c monotonicity: val^out_t(Z) ≤ val^in_t(Phi*(Z)) for every bounded Z (t ≥ 0). -/
theorem val_mono (Phi : Channel I J) (rho sigma : State I)
    {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr1' : Summable r0)
    (hev' : ∀ i, boundedOperator (Phi.val rho.coefficients) (e0 i) = (r0 i : ℂ) • e0 i)
    (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (hfv' : ∀ j, boundedOperator (Phi.val sigma.coefficients) (f0 j) = (s0 j : ℂ) • f0 j)
    (t : ℝ) (ht : 0 ≤ t) (Z : Hilbert J →L[ℂ] Hilbert J) :
    val e0 f0 r0 s0 t Z ≤ val e f r s t (channelDual Phi.val Z) := by
  rw [val_tr ⟨_, chan_density Phi.val Phi.property _ rho.density⟩
      ⟨_, chan_density Phi.val Phi.property _ sigma.density⟩ e0 f0 r0 s0 hr0' hr1' hev' hs0' hs1'
      hfv' t Z,
    val_tr rho sigma e f r s hr0 hr1 hev hs0 hs1 hfv t (channelDual Phi.val Z)]
  have k1 := ks_trace Phi rho Z
  have k2 := ks_trace Phi sigma (ContinuousLinearMap.adjoint Z)
  rw [dual_adj] at k1 ⊢
  rw [dual_pair Phi _ _ rho.density.1]
  dsimp only
  linarith [mul_le_mul_of_nonneg_left k1 ht, k2]

/-- K-c: Q_t decreases under channels, Q_t(Phi rho, Phi sigma) ≤ Q_t(rho, sigma) (t > 0). -/
theorem Q_mono (Phi : Channel I J) (rho sigma : State I)
    {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr1' : Summable r0)
    (hev' : ∀ i, boundedOperator (Phi.val rho.coefficients) (e0 i) = (r0 i : ℂ) • e0 i)
    (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (hfv' : ∀ j, boundedOperator (Phi.val sigma.coefficients) (f0 j) = (s0 j : ℂ) • f0 j)
    (t : ℝ) (ht : 0 < t) :
    Qv e0 f0 r0 s0 t ≤ Qv e f r s t :=
  le_of_tendsto' (val_trunc_tendsto e0 f0 hr0' hs0' hr1' hs1' ht) (fun F =>
    (val_mono Phi rho sigma e f r s hr0 hr1 hev hs0 hs1 hfv e0 f0 r0 s0 hr0' hr1' hev' hs0' hs1'
      hfv' t ht.le _).trans (val_le e f hr0 hs0 hr1 hs1 ht _))

end P45C4C

end

end C4cPart


/-! ## C4 K-b (s13+): Tonelli step b1. Iteration file importing laptop module P45S.C4c. -/
section C4dPart

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace P45C4D

open MeasureTheory Set Filter Topology
open P45C4 P45C4C P45KB
open scoped InnerProductSpace

/-- Lindblad's scalar kernel with Mathlib's log conventions (log 0 = 0). -/
def eta (r s : ℝ) : ℝ := r * Real.log r - r * Real.log s + s - r

lemma kbK_meas (r s : ℝ) : Measurable (kbK r s) := by
  unfold kbK; fun_prop

lemma kbK_nonneg' {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 < t) : 0 ≤ kbK r s t := by
  unfold kbK; positivity

lemma kb_term_lint {r s c : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hdeg : s = 0 → c = 0 ∨ r = 0) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * kbK r s t) = ENNReal.ofReal (c * eta r s) := by
  rcases hs.lt_or_eq with hs' | hs'
  · simp_rw [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, kb_scalar_lint hr hs']
    rfl
  · rcases hdeg hs'.symm with h | h
    · subst h; simp
    · subst h; subst hs'; simp [kbK, eta]

variable {E ι κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma cA_hasSum (e : HilbertBasis ι ℂ E) (f : HilbertBasis κ ℂ E) (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) {R : ℝ} (hR : HasSum r R) :
    HasSum (fun p : κ × ι => ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2) R := by
  have hfa : ∀ i, HasSum (fun j => ‖⟪f j, e i⟫_ℂ‖ ^ 2 * r i) (r i) := by
    intro i
    have h := (hb_norm_sq f (e i)).mul_right (r i)
    rwa [e.orthonormal.1 i, one_pow, one_mul] at h
  have h := hasSum_prod_of_fibers_nonneg' (f := fun p : κ × ι => ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2)
    (fun p => mul_nonneg (sq_nonneg _) (hr _)) (g := r) hfa hR.summable
  rwa [hR.tsum_eq] at h

end P45C4D

end

end C4dPart


/-! ## C4 K-b step b2 (s14): finite-dimensional eigen formula of Lindblad's relative entropy.
Independent of the C4b..C4d layers (imports only Mathlib + Definitions). -/
section C4ePart

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped BigOperators ComplexOrder Matrix

namespace P45C4E

open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy)
open P45KB

variable {F : Type} [Fintype F] [DecidableEq F]

/-- Lindblad's scalar kernel (same as `P45C4D.eta`). -/
def etaE (r s : ℝ) : ℝ := r * Real.log r - r * Real.log s + s - r

lemma etaE_nonneg {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) : 0 ≤ etaE r s := by
  unfold etaE
  rcases hr.lt_or_eq with hr' | hr'
  · have h := Real.one_sub_inv_le_log_of_pos (show 0 < r / s by positivity)
    rw [Real.log_div hr'.ne' hs.ne', inv_div] at h
    have h2 : r * (1 - s / r) ≤ r * (Real.log r - Real.log s) := mul_le_mul_of_nonneg_left h hr
    have h3 : r * (1 - s / r) = r - s := by field_simp
    nlinarith
  · subst hr'; simp; linarith

/-- Overlap matrix of the two eigenbases: `Mc i j = <e_i, f_j>`. -/
def Mc {A B : Matrix F F ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) : Matrix F F ℂ :=
  star (hA.eigenvectorUnitary : Matrix F F ℂ) * (hB.eigenvectorUnitary : Matrix F F ℂ)

lemma tr_cfc_cfc {A B : Matrix F F ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h g : ℝ → ℝ) :
    (cfc h A * cfc g B).trace.re =
      ∑ i, ∑ j, ‖Mc hA hB i j‖ ^ 2 * (h (hA.eigenvalues i) * g (hB.eigenvalues j)) := by
  rw [hA.cfc_eq, hB.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  set UA : Matrix F F ℂ := (hA.eigenvectorUnitary : Matrix F F ℂ)
  set UB : Matrix F F ℂ := (hB.eigenvectorUnitary : Matrix F F ℂ)
  set DA := Matrix.diagonal (RCLike.ofReal ∘ h ∘ hA.eigenvalues : F → ℂ)
  set DB := Matrix.diagonal (RCLike.ofReal ∘ g ∘ hB.eigenvalues : F → ℂ)
  have hcyc : (UA * DA * star UA * (UB * DB * star UB)).trace =
      (DA * (star UA * UB) * DB * (star UB * UA)).trace := by
    rw [show UA * DA * star UA * (UB * DB * star UB) =
        UA * (DA * (star UA * UB) * DB * star UB) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hst : star UB * UA = star (Mc hA hB) := by
    show star UB * UA = star (star UA * UB)
    rw [star_mul, star_star]
  rw [hcyc, hst, show star UA * UB = Mc hA hB from rfl]
  have hX : ∀ i k, (DA * Mc hA hB * DB) i k =
      (h (hA.eigenvalues i) : ℂ) * Mc hA hB i k * (g (hB.eigenvalues k) : ℂ) := by
    intro i k
    simp [DA, DB, Matrix.mul_diagonal, Matrix.diagonal_mul]
  generalize DA * Mc hA hB * DB = X at hX
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, hX, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hn : (Mc hA hB i j) * star (Mc hA hB i j) = ((‖Mc hA hB i j‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc ((h (hA.eigenvalues i) : ℂ) * Mc hA hB i j * (g (hB.eigenvalues j) : ℂ) *
        star (Mc hA hB i j)).re
      = (((‖Mc hA hB i j‖ ^ 2 * (h (hA.eigenvalues i) * g (hB.eigenvalues j)) : ℝ)) : ℂ).re := by
        congr 1
        rw [show (h (hA.eigenvalues i) : ℂ) * Mc hA hB i j * (g (hB.eigenvalues j) : ℂ) *
            star (Mc hA hB i j) = (Mc hA hB i j * star (Mc hA hB i j)) *
            ((h (hA.eigenvalues i) : ℂ) * (g (hB.eigenvalues j) : ℂ)) by ring, hn]
        push_cast; ring
    _ = _ := Complex.ofReal_re _

/-- Indicator of the kernel eigenvalue `0`. -/
def ind0 (x : ℝ) : ℝ := if x = 0 then 1 else 0

lemma B_mul_ind {B : Matrix F F ℂ} (hB : B.IsHermitian) : B * cfc ind0 B = 0 := by
  have h := cfc_mul (fun x : ℝ => x) ind0 B (by fun_prop)
    (Matrix.finite_real_spectrum.continuousOn _)
  rw [cfc_id' ℝ B] at h
  rw [← h]
  have : (fun x : ℝ => x * ind0 x) = fun _ => 0 := by
    funext x; by_cases hx : x = 0 <;> simp [ind0, hx]
  rw [this, cfc_const_zero]

lemma A_mul_ind {A B : Matrix F F ℂ} (hB : B.IsHermitian)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) : A * cfc ind0 B = 0 := by
  have key : ∀ v : F → ℂ, (A * cfc ind0 B) *ᵥ v = 0 := by
    intro v
    rw [← Matrix.mulVec_mulVec]
    have hv : cfc ind0 B *ᵥ v ∈ LinearMap.ker B.mulVecLin := by
      simp [Matrix.mulVec_mulVec, B_mul_ind hB]
    simpa using hker hv
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

lemma ker_coeff {A B : Matrix F F ℂ} (hA : A.PosSemidef) (hB : B.IsHermitian)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) (i j : F)
    (hj : hB.eigenvalues j = 0) : ‖Mc hA.isHermitian hB i j‖ ^ 2 * hA.isHermitian.eigenvalues i = 0 := by
  have h := tr_cfc_cfc hA.isHermitian hB (fun x => x) ind0
  rw [cfc_id' ℝ A hA.isHermitian.isSelfAdjoint, A_mul_ind hB hker, Matrix.trace_zero, Complex.zero_re] at h
  have hnn : ∀ i j, 0 ≤ ‖Mc hA.isHermitian hB i j‖ ^ 2 *
      (hA.isHermitian.eigenvalues i * ind0 (hB.eigenvalues j)) := by
    intro i j
    refine mul_nonneg (sq_nonneg _) (mul_nonneg (hA.eigenvalues_nonneg i) ?_)
    unfold ind0; split_ifs <;> norm_num
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)).mp
    h.symm i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).mp h1 j (Finset.mem_univ _)
  simpa [ind0, hj] using h2

/-- K-b step b2: Lindblad's finite relative entropy in the two eigenbases. -/
theorem fre_eigen {A B : Matrix F F ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    finiteRelativeEntropy A B = ∑ i, ∑ j, ENNReal.ofReal (‖Mc hA.isHermitian hB.isHermitian i j‖ ^ 2 *
      etaE (hA.isHermitian.eigenvalues i) (hB.isHermitian.eigenvalues j)) := by
  set hA' := hA.isHermitian
  set hB' := hB.isHermitian
  have t1 : (A * cfc Real.log A).trace.re = ∑ i, ∑ j, ‖Mc hA' hB' i j‖ ^ 2 *
      ((fun x => x * Real.log x) (hA'.eigenvalues i) * (fun _ => (1:ℝ)) (hB'.eigenvalues j)) := by
    have h := tr_cfc_cfc hA' hB' (fun x => x * Real.log x) (fun _ => 1)
    rw [cfc_const_one ℝ B, Matrix.mul_one,
      cfc_mul (fun x : ℝ => x) Real.log A (by fun_prop) (Matrix.finite_real_spectrum.continuousOn _),
      cfc_id' ℝ A] at h
    exact h
  have t2 : (A * cfc Real.log B).trace.re = ∑ i, ∑ j, ‖Mc hA' hB' i j‖ ^ 2 *
      ((fun x => x) (hA'.eigenvalues i) * Real.log (hB'.eigenvalues j)) := by
    have h := tr_cfc_cfc hA' hB' (fun x => x) Real.log
    rw [cfc_id' ℝ A] at h
    exact h
  have t3 : B.trace.re = ∑ i, ∑ j, ‖Mc hA' hB' i j‖ ^ 2 *
      ((fun _ => (1:ℝ)) (hA'.eigenvalues i) * (fun x => x) (hB'.eigenvalues j)) := by
    have h := tr_cfc_cfc hA' hB' (fun _ => 1) (fun x => x)
    rw [cfc_const_one ℝ A, cfc_id' ℝ B, Matrix.one_mul] at h
    exact h
  have t4 : A.trace.re = ∑ i, ∑ j, ‖Mc hA' hB' i j‖ ^ 2 *
      ((fun x => x) (hA'.eigenvalues i) * (fun _ => (1:ℝ)) (hB'.eigenvalues j)) := by
    have h := tr_cfc_cfc hA' hB' (fun x => x) (fun _ => 1)
    rw [cfc_const_one ℝ B, cfc_id' ℝ A, Matrix.mul_one] at h
    exact h
  have hval : (A * cfc Real.log A - A * cfc Real.log B + B - A).trace.re =
      ∑ i, ∑ j, ‖Mc hA' hB' i j‖ ^ 2 * etaE (hA'.eigenvalues i) (hB'.eigenvalues j) := by
    simp only [Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
    rw [t1, t2, t3, t4, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold etaE; ring
  have hnn : ∀ i j, 0 ≤ ‖Mc hA' hB' i j‖ ^ 2 * etaE (hA'.eigenvalues i) (hB'.eigenvalues j) := by
    intro i j
    rcases (hB.eigenvalues_nonneg j).lt_or_eq with hs | hs
    · exact mul_nonneg (sq_nonneg _) (etaE_nonneg (hA.eigenvalues_nonneg i) hs)
    · have hk := ker_coeff hA hB' hker i j hs.symm
      rcases mul_eq_zero.mp hk with h | h
      · rw [h, zero_mul]
      · rw [h, ← hs]; simp [etaE]
  unfold finiteRelativeEntropy
  rw [if_pos hker, hval, ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => hnn i j]

/-! ### P2f: finite-dimensional variational form of the Lindblad integrand. -/

section Var

variable {A B : Matrix F F ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)

/-- Shifted resolvent functional, c = 1/(1+t). -/
def gfin (A B : Matrix F F ℂ) (t : ℝ) (V : Matrix F F ℂ) : ℝ :=
  2 / (1 + t) * ((A - B) * V).trace.re - (B * V * Vᴴ).trace.re - t * (A * Vᴴ * V).trace.re

/-- Its optimum, Sum |c_ij|^2 kbK(r_i, s_j, t). -/
def jfin (t : ℝ) : ℝ := ∑ i, ∑ j, ‖Mc hA hB i j‖ ^ 2 * kbK (hA.eigenvalues i) (hB.eigenvalues j) t

/-- Coordinates of V between the eigenbases: Xc j i = <f_j, V e_i>. -/
def Xc (V : Matrix F F ℂ) : Matrix F F ℂ :=
  star (hB.eigenvectorUnitary : Matrix F F ℂ) * V * (hA.eigenvectorUnitary : Matrix F F ℂ)

lemma uu {G : Matrix F F ℂ} (hG : G.IsHermitian) :
    star (hG.eigenvectorUnitary : Matrix F F ℂ) * (hG.eigenvectorUnitary : Matrix F F ℂ) = 1 :=
  Unitary.star_mul_self_of_mem hG.eigenvectorUnitary.2

lemma uu' {G : Matrix F F ℂ} (hG : G.IsHermitian) :
    (hG.eigenvectorUnitary : Matrix F F ℂ) * star (hG.eigenvectorUnitary : Matrix F F ℂ) = 1 :=
  Unitary.mul_star_self_of_mem hG.eigenvectorUnitary.2

lemma spec' {G : Matrix F F ℂ} (hG : G.IsHermitian) :
    G = (hG.eigenvectorUnitary : Matrix F F ℂ) * Matrix.diagonal (RCLike.ofReal ∘ hG.eigenvalues) *
      star (hG.eigenvectorUnitary : Matrix F F ℂ) := by
  conv_lhs => rw [hG.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]

lemma V_eq (V : Matrix F F ℂ) :
    V = (hB.eigenvectorUnitary : Matrix F F ℂ) * Xc hA hB V * star (hA.eigenvectorUnitary : Matrix F F ℂ) := by
  simp only [Xc, ← Matrix.mul_assoc, uu' hB, Matrix.one_mul]
  rw [Matrix.mul_assoc, uu' hA, Matrix.mul_one]

lemma tr_diag (d : F → ℂ) (Y : Matrix F F ℂ) : (Matrix.diagonal d * Y).trace = ∑ i, d i * Y i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

lemma tr_conj (U Y : Matrix F F ℂ) (hU : star U * U = 1) : (U * Y * star U).trace = Y.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

lemma T1 (V : Matrix F F ℂ) : (A * V).trace =
    ∑ i, (hA.eigenvalues i : ℂ) * ∑ j, Mc hA hB i j * Xc hA hB V j i := by
  set UA : Matrix F F ℂ := (hA.eigenvectorUnitary : Matrix F F ℂ)
  set UB : Matrix F F ℂ := (hB.eigenvectorUnitary : Matrix F F ℂ)
  have e : A * V = UA * (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (Mc hA hB * Xc hA hB V)) *
      star UA := by
    conv_lhs => rw [spec' hA, V_eq hA hB V]
    simp only [Mc, Matrix.mul_assoc, UA, UB]
  rw [e, tr_conj _ _ (uu hA), tr_diag]
  simp [Matrix.mul_apply]

lemma T2 (V : Matrix F F ℂ) : (B * V).trace =
    ∑ j, (hB.eigenvalues j : ℂ) * ∑ i, Xc hA hB V j i * Mc hA hB i j := by
  set UA : Matrix F F ℂ := (hA.eigenvectorUnitary : Matrix F F ℂ)
  set UB : Matrix F F ℂ := (hB.eigenvectorUnitary : Matrix F F ℂ)
  have e : B * V = UB * (Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) * (Xc hA hB V * Mc hA hB)) *
      star UB := by
    conv_lhs => rw [spec' hB, V_eq hA hB V]
    simp only [Mc, Matrix.mul_assoc, UA, UB]
    rw [← Matrix.mul_assoc (star (hB.eigenvectorUnitary : Matrix F F ℂ)), uu hB, Matrix.one_mul,
      uu' hB, Matrix.mul_one]
  rw [e, tr_conj _ _ (uu hB), tr_diag]
  simp [Matrix.mul_apply]

lemma T3 (V : Matrix F F ℂ) : (B * V * Vᴴ).trace.re =
    ∑ j, hB.eigenvalues j * ∑ i, ‖Xc hA hB V j i‖ ^ 2 := by
  set UA : Matrix F F ℂ := (hA.eigenvectorUnitary : Matrix F F ℂ)
  set UB : Matrix F F ℂ := (hB.eigenvectorUnitary : Matrix F F ℂ)
  set X := Xc hA hB V
  have hVh : Vᴴ = UA * Xᴴ * star UB := by
    conv_lhs => rw [V_eq hA hB V]
    simp only [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, star_star, Matrix.mul_assoc, UA, UB, X]
    rw [star_mul, star_mul, star_star, Matrix.mul_assoc]
  have e : B * V * Vᴴ = UB * (Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) * (X * Xᴴ)) * star UB := by
    rw [hVh]
    conv_lhs => rw [spec' hB, V_eq hA hB V]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star UB) UB, uu hB, Matrix.one_mul,
      ← Matrix.mul_assoc (star UA) UA, uu hA, Matrix.one_mul]
  rw [e, tr_conj _ _ (uu hB), tr_diag, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  show ((hB.eigenvalues j : ℂ) * ((‖X j i‖ ^ 2 : ℝ) : ℂ)).re = _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

lemma T4 (V : Matrix F F ℂ) : (A * Vᴴ * V).trace.re =
    ∑ i, hA.eigenvalues i * ∑ j, ‖Xc hA hB V j i‖ ^ 2 := by
  set UA : Matrix F F ℂ := (hA.eigenvectorUnitary : Matrix F F ℂ)
  set UB : Matrix F F ℂ := (hB.eigenvectorUnitary : Matrix F F ℂ)
  set X := Xc hA hB V
  have hVh : Vᴴ = UA * Xᴴ * star UB := by
    conv_lhs => rw [V_eq hA hB V]
    simp only [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, star_star, Matrix.mul_assoc, UA, UB, X]
    rw [star_mul, star_mul, star_star, Matrix.mul_assoc]
  have e : A * Vᴴ * V = UA * (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * (Xᴴ * X)) * star UA := by
    rw [hVh]
    conv_lhs => rw [spec' hA, V_eq hA hB V]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star UA) UA, uu hA, Matrix.one_mul,
      ← Matrix.mul_assoc (star UB) UB, uu hB, Matrix.one_mul]
  rw [e, tr_conj _ _ (uu hA), tr_diag, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, mul_comm (starRingEnd ℂ _), Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  show ((hA.eigenvalues i : ℂ) * ((‖X j i‖ ^ 2 : ℝ) : ℂ)).re = _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

lemma gfin_eq (t : ℝ) (V : Matrix F F ℂ) : gfin A B t V =
    ∑ i, ∑ j, (2 / (1 + t) * ((hA.eigenvalues i - hB.eigenvalues j) *
      (Mc hA hB i j * Xc hA hB V j i).re) - (hB.eigenvalues j + t * hA.eigenvalues i) *
        ‖Xc hA hB V j i‖ ^ 2) := by
  set r := hA.eigenvalues
  set q := hB.eigenvalues
  set M := Mc hA hB
  set X := Xc hA hB V
  have h1 : ((A * V).trace).re = ∑ i, ∑ j, r i * (M i j * X j i).re := by
    rw [T1 hA hB, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
  have h2 : ((B * V).trace).re = ∑ i, ∑ j, q j * (M i j * X j i).re := by
    rw [T2 hA hB, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (X j i)]
  have h3 : (B * V * Vᴴ).trace.re = ∑ i, ∑ j, q j * ‖X j i‖ ^ 2 := by
    rw [T3 hA hB, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have h4 : (A * Vᴴ * V).trace.re = ∑ i, ∑ j, r i * ‖X j i‖ ^ 2 := by
    rw [T4 hA hB]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  unfold gfin
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, h1, h2, h3, h4]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma ent_le {r q t : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (ht : 0 < t) (m x : ℂ) :
    2 / (1 + t) * ((r - q) * (m * x).re) - (q + t * r) * ‖x‖ ^ 2 ≤ ‖m‖ ^ 2 * kbK r q t := by
  unfold kbK
  have hu : (r - q) * (m * x).re ≤ |r - q| * ‖m‖ * ‖x‖ := by
    calc (r - q) * (m * x).re ≤ |(r - q) * (m * x).re| := le_abs_self _
      _ = |r - q| * |(m * x).re| := abs_mul _ _
      _ ≤ |r - q| * ‖m * x‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
      _ = |r - q| * ‖m‖ * ‖x‖ := by rw [norm_mul, mul_assoc]
  have h1t : 0 < 1 + t := by linarith
  rcases (show 0 ≤ q + t * r by positivity).lt_or_eq with hd | hd
  · set c := 1 / (1 + t) with hc
    set w := |r - q| * ‖m‖ with hw
    have hc0 : 0 < c := by positivity
    have e1 : 2 / (1 + t) = 2 * c := by rw [hc]; ring
    have e2 : ‖m‖ ^ 2 * ((r - q) ^ 2 / ((q + t * r) * (1 + t) ^ 2)) = (c * w) ^ 2 / (q + t * r) := by
      rw [hw, hc, mul_pow, mul_pow, sq_abs]; field_simp
    rw [e1, e2, le_div_iff₀ hd]
    have hy := norm_nonneg x
    have : 2 * c * ((r - q) * (m * x).re) ≤ 2 * c * (w * ‖x‖) := by
      rw [hw]; nlinarith
    nlinarith [sq_nonneg (c * w - (q + t * r) * ‖x‖)]
  · have hr0 : r = 0 := by nlinarith
    have hq0 : q = 0 := by nlinarith
    subst hr0; subst hq0; simp

/-- P2f upper bound: the finite variational functional never exceeds jfin. -/
theorem gfin_le {t : ℝ} (ht : 0 < t) (hA0 : ∀ i, 0 ≤ hA.eigenvalues i) (hB0 : ∀ j, 0 ≤ hB.eigenvalues j)
    (V : Matrix F F ℂ) : gfin A B t V ≤ jfin hA hB t := by
  rw [gfin_eq hA hB, jfin]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ent_le (hA0 i) (hB0 j) ht _ _

/-- The optimiser in eigen coordinates. -/
def Xopt (t : ℝ) : Matrix F F ℂ := fun j i =>
  (((1 / (1 + t)) * (hA.eigenvalues i - hB.eigenvalues j) /
    (hB.eigenvalues j + t * hA.eigenvalues i) : ℝ) : ℂ) * star (Mc hA hB i j)

lemma ent_eq {r q t : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (ht : 0 < t) (m : ℂ) :
    2 / (1 + t) * ((r - q) * (m * ((((1 / (1 + t)) * (r - q) / (q + t * r) : ℝ) : ℂ) * star m)).re)
      - (q + t * r) * ‖(((1 / (1 + t)) * (r - q) / (q + t * r) : ℝ) : ℂ) * star m‖ ^ 2
      = ‖m‖ ^ 2 * kbK r q t := by
  unfold kbK
  have h1t : 0 < 1 + t := by linarith
  have hmm : (m * star m).re = ‖m‖ ^ 2 := by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hre : (m * ((((1 / (1 + t)) * (r - q) / (q + t * r) : ℝ) : ℂ) * star m)).re =
      (1 / (1 + t)) * (r - q) / (q + t * r) * ‖m‖ ^ 2 := by
    rw [mul_left_comm, Complex.re_ofReal_mul, hmm]
  have hn : ‖(((1 / (1 + t)) * (r - q) / (q + t * r) : ℝ) : ℂ) * star m‖ ^ 2 =
      ((1 / (1 + t)) * (r - q) / (q + t * r)) ^ 2 * ‖m‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star, mul_pow, sq_abs]
  rw [hre, hn]
  rcases (show 0 ≤ q + t * r by positivity).lt_or_eq with hd | hd
  · field_simp; ring
  · rw [← hd]; simp

lemma Xc_opt (t : ℝ) : Xc hA hB ((hB.eigenvectorUnitary : Matrix F F ℂ) * Xopt hA hB t *
    star (hA.eigenvectorUnitary : Matrix F F ℂ)) = Xopt hA hB t := by
  simp only [Xc, ← Matrix.mul_assoc, uu hB, Matrix.one_mul]
  rw [Matrix.mul_assoc, uu hA, Matrix.mul_one]

/-- P2f attainment: jfin is the maximum of gfin. -/
theorem gfin_opt {t : ℝ} (ht : 0 < t) (hA0 : ∀ i, 0 ≤ hA.eigenvalues i) (hB0 : ∀ j, 0 ≤ hB.eigenvalues j) :
    gfin A B t ((hB.eigenvectorUnitary : Matrix F F ℂ) * Xopt hA hB t *
      star (hA.eigenvectorUnitary : Matrix F F ℂ)) = jfin hA hB t := by
  rw [gfin_eq hA hB, Xc_opt, jfin]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact ent_eq (hA0 i) (hB0 j) ht _

end Var

open MeasureTheory Set in
/-- K-b P1: Lindblad's finite entropy is the integral of the finite resolvent integrand. -/
theorem fre_lint {A B : Matrix F F ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    finiteRelativeEntropy A B =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (jfin hA.isHermitian hB.isHermitian t) := by
  set hA' := hA.isHermitian
  set hB' := hB.isHermitian
  have hr := hA.eigenvalues_nonneg
  have hs := hB.eigenvalues_nonneg
  rw [fre_eigen hA hB hker]
  have hterm : ∀ i j, ENNReal.ofReal (‖Mc hA' hB' i j‖ ^ 2 * etaE (hA'.eigenvalues i) (hB'.eigenvalues j)) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖Mc hA' hB' i j‖ ^ 2 *
        kbK (hA'.eigenvalues i) (hB'.eigenvalues j) t) := by
    intro i j
    rw [P45C4D.kb_term_lint (sq_nonneg _) (hr i) (hs j)]
    · rfl
    · intro h0
      rcases mul_eq_zero.mp (ker_coeff hA hB' hker i j h0) with h | h
      · exact Or.inl h
      · exact Or.inr h
  simp_rw [hterm]
  have hmeas : ∀ i j, Measurable fun t => ENNReal.ofReal (‖Mc hA' hB' i j‖ ^ 2 *
      kbK (hA'.eigenvalues i) (hB'.eigenvalues j) t) := fun i j =>
    ENNReal.measurable_ofReal.comp ((P45C4D.kbK_meas _ _).const_mul _)
  have hin : ∀ i, ∑ j, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖Mc hA' hB' i j‖ ^ 2 *
      kbK (hA'.eigenvalues i) (hB'.eigenvalues j) t) = ∫⁻ t in Ioi (0 : ℝ), ∑ j,
        ENNReal.ofReal (‖Mc hA' hB' i j‖ ^ 2 * kbK (hA'.eigenvalues i) (hB'.eigenvalues j) t) :=
    fun i => (lintegral_finset_sum _ fun j _ => hmeas i j).symm
  simp_rw [hin]
  rw [← lintegral_finset_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hmeas i j]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  unfold jfin
  have hnn : ∀ i j, 0 ≤ ‖Mc hA' hB' i j‖ ^ 2 * kbK (hA'.eigenvalues i) (hB'.eigenvalues j) t :=
    fun i j => mul_nonneg (sq_nonneg _) (P45C4D.kbK_nonneg' (hr i) (hs j) ht)
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => hnn i j]

end P45C4E

end

end C4ePart


/-! ## C4 K-b P2e/P2u/P2l (s15): compressions of the Hilbert-space resolvent functional.
Iteration file: imports the laptop-built olean P45S.C4e. -/
section C4fPart

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

namespace P45C4F

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open P45Petz P45C4 P45C4B

variable {I : Type}

/-! ### Coordinate projections. -/

/-- Coordinate projection onto the finite set s. -/
def Ps (s : Finset I) : Hilbert I →L[ℂ] Hilbert I :=
  ∑ k ∈ s, InnerProductSpace.rankOne ℂ (stdB I k) (stdB I k)

lemma Ps_apply (s : Finset I) (x : Hilbert I) :
    Ps s x = ∑ k ∈ s, ⟪stdB I k, x⟫_ℂ • stdB I k := by
  simp [Ps, InnerProductSpace.rankOne_apply]

lemma inner_Ps (s : Finset I) (k : I) (x : Hilbert I) :
    ⟪stdB I k, Ps s x⟫_ℂ = if k ∈ s then ⟪stdB I k, x⟫_ℂ else 0 := by
  rw [Ps_apply, inner_sum]
  simp_rw [inner_smul_right, orthonormal_iff_ite.mp (stdB I).orthonormal k]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]

lemma Ps_sym (s : Finset I) (x y : Hilbert I) : ⟪Ps s x, y⟫_ℂ = ⟪x, Ps s y⟫_ℂ := by
  rw [Ps_apply, Ps_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]

lemma Ps_adj (s : Finset I) : ContinuousLinearMap.adjoint (Ps s) = Ps s :=
  ((ContinuousLinearMap.eq_adjoint_iff (Ps s) (Ps s)).mpr (Ps_sym s)).symm

lemma Ps_idem (s : Finset I) (x : Hilbert I) : Ps s (Ps s x) = Ps s x := by
  rw [Ps_apply s (Ps s x)]
  conv_rhs => rw [Ps_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [inner_Ps, if_pos hk]

lemma Ps_norm (s : Finset I) (x : Hilbert I) : ‖Ps s x‖ ≤ ‖x‖ := by
  have h : ⟪Ps s x, Ps s x⟫_ℂ = ⟪x, Ps s x⟫_ℂ := by rw [Ps_sym, Ps_idem]
  have h1 : ‖Ps s x‖ ^ 2 = RCLike.re ⟪x, Ps s x⟫_ℂ := by
    rw [← h, inner_self_eq_norm_sq (𝕜 := ℂ)]
  have h2 := re_inner_le_norm (𝕜 := ℂ) x (Ps s x)
  nlinarith [norm_nonneg (Ps s x), norm_nonneg x]

lemma Ps_tendsto (x : Hilbert I) :
    Filter.Tendsto (fun s : Finset I => Ps s x) Filter.atTop (nhds x) := by
  have h : HasSum (fun k => ⟪stdB I k, x⟫_ℂ • stdB I k) x := by
    simpa only [HilbertBasis.repr_apply_apply] using (stdB I).hasSum_repr x
  simp_rw [Ps_apply]
  exact h

/-- P_s (W (P_s x)) → W x. -/
lemma PWP_tendsto (W : Hilbert I →L[ℂ] Hilbert I) (x : Hilbert I) :
    Filter.Tendsto (fun s : Finset I => Ps s (W (Ps s x))) Filter.atTop (nhds (W x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp (Ps_tendsto x)).const_mul ‖W‖
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (Ps_tendsto (W x))
  rw [mul_zero] at h1
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) h3
  have e : Ps s (W (Ps s x)) - W x = Ps s (W (Ps s x - x)) + (Ps s (W x) - W x) := by
    simp only [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
  exact (Ps_norm s _).trans (W.le_opNorm _)

/-! ### The trace pairing of a state as a linear functional. -/

lemma L_add (rho : State I) (W1 W2 : Hilbert I →L[ℂ] Hilbert I) :
    boundedTracePair rho.coefficients (W1 + W2) =
      boundedTracePair rho.coefficients W1 + boundedTracePair rho.coefficients W2 := by
  obtain ⟨ι, e, r, hr0, hr1, hev⟩ := state_eigen rho
  have h := (pair_eigen rho e r hr0 hr1.summable hev W1).add (pair_eigen rho e r hr0 hr1.summable hev W2)
  refine (pair_eigen rho e r hr0 hr1.summable hev (W1 + W2)).unique (h.congr_fun fun i => ?_)
  simp [inner_add_right, mul_add]

lemma L_smul (rho : State I) (a : ℂ) (W : Hilbert I →L[ℂ] Hilbert I) :
    boundedTracePair rho.coefficients (a • W) = a * boundedTracePair rho.coefficients W := by
  obtain ⟨ι, e, r, hr0, hr1, hev⟩ := state_eigen rho
  have h := (pair_eigen rho e r hr0 hr1.summable hev W).mul_left a
  refine (pair_eigen rho e r hr0 hr1.summable hev (a • W)).unique (h.congr_fun fun i => ?_)
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right]
  ring

lemma L_one (rho : State I) : boundedTracePair rho.coefficients (ContinuousLinearMap.id ℂ _) = 1 := by
  obtain ⟨ι, e, r, hr0, hr1, hev⟩ := state_eigen rho
  have h := Complex.hasSum_ofReal.mpr hr1
  refine (pair_eigen rho e r hr0 hr1.summable hev _).unique (h.congr_fun fun i => ?_)
  simp [inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]

lemma L_adj_re (rho : State I) (W : Hilbert I →L[ℂ] Hilbert I) :
    (boundedTracePair rho.coefficients (ContinuousLinearMap.adjoint W)).re =
      (boundedTracePair rho.coefficients W).re := by
  obtain ⟨ι, e, r, hr0, hr1, hev⟩ := state_eigen rho
  have h1 := Complex.hasSum_re (pair_eigen rho e r hr0 hr1.summable hev W)
  have h2 := Complex.hasSum_re (pair_eigen rho e r hr0 hr1.summable hev (ContinuousLinearMap.adjoint W))
  refine h2.unique (h1.congr_fun fun i => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    ← inner_conj_symm (W (e i)) (e i), Complex.conj_re]

/-! ### P2u: the shifted functional G_t is bounded by J_t = Q_t - 1/(1+t). -/

/-- G_t(W) = 2c Re Tr((rho - sigma) W) - Tr(sigma W W*) - t Tr(rho W* W), c = 1/(1+t). -/
def Gt (rho sigma : State I) (t : ℝ) (W : Hilbert I →L[ℂ] Hilbert I) : ℝ :=
  2 / (1 + t) * (boundedTracePair rho.coefficients W - boundedTracePair sigma.coefficients W).re
    - (boundedTracePair sigma.coefficients (W.comp (ContinuousLinearMap.adjoint W))).re
    - t * (boundedTracePair rho.coefficients ((ContinuousLinearMap.adjoint W).comp W)).re

lemma L_shift_re (rho : State I) (c : ℝ) (W : Hilbert I →L[ℂ] Hilbert I) :
    (boundedTracePair rho.coefficients ((c : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + W)).re =
      c + (boundedTracePair rho.coefficients W).re := by
  rw [L_add, L_smul, L_one]; simp

lemma adj_shift (c : ℝ) (W : Hilbert I →L[ℂ] Hilbert I) :
    ContinuousLinearMap.adjoint ((c : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + W) =
      (c : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + ContinuousLinearMap.adjoint W := by
  rw [map_add, map_smulₛₗ, ContinuousLinearMap.adjoint_id]
  simp

lemma comp_shift (c : ℝ) (W X : Hilbert I →L[ℂ] Hilbert I) :
    ((c : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + W).comp
        ((c : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + X) =
      ((c ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + (c : ℂ) • X + (c : ℂ) • W + W.comp X := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_add, map_smul]
  push_cast
  module

lemma L_comp_shift_re (rho : State I) (c : ℝ) (W X : Hilbert I →L[ℂ] Hilbert I) :
    (boundedTracePair rho.coefficients (((c : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + W).comp
        ((c : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + X))).re =
      c ^ 2 + c * (boundedTracePair rho.coefficients X).re + c * (boundedTracePair rho.coefficients W).re
        + (boundedTracePair rho.coefficients (W.comp X)).re := by
  rw [comp_shift, L_add, L_add, L_add, L_smul, L_smul, L_smul, L_one]
  simp only [Complex.add_re, Complex.re_ofReal_mul, mul_one, Complex.ofReal_re]

/-- val at the shifted operator (1+t)⁻¹ + W is (1+t)⁻¹ + G_t(W). -/
theorem val_shift (rho sigma : State I) {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I))
    (f : HilbertBasis κ ℂ (Hilbert I)) (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    {t : ℝ} (ht : 0 < t) (W : Hilbert I →L[ℂ] Hilbert I) :
    val e f r s t ((((1 + t)⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + W) =
      (1 + t)⁻¹ + Gt rho sigma t W := by
  set u : ℝ := (1 + t)⁻¹ with hu
  have ht1 : (1 + t) ≠ 0 := by linarith
  have hc : u * (1 + t) = 1 := inv_mul_cancel₀ ht1
  have hv := P45C4C.val_tr rho sigma e f r s hr0 hr1 hev hs0 hs1 hfv t
    ((u : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + W)
  rw [ContinuousLinearMap.adjoint_adjoint, adj_shift, L_comp_shift_re, L_comp_shift_re,
    L_shift_re, L_adj_re, L_adj_re] at hv
  have h2 : 2 / (1 + t) = 2 * u := by rw [hu, div_eq_mul_inv]
  rw [hv]
  unfold Gt
  rw [h2, Complex.sub_re]
  linear_combination (-(u + 2 * (boundedTracePair rho.coefficients W).re)) * hc

/-- P2u: G_t(W) ≤ Q_t - 1/(1+t) for states, t > 0. -/
theorem Gt_le (rho sigma : State I) {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I))
    (f : HilbertBasis κ ℂ (Hilbert I)) (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    {t : ℝ} (ht : 0 < t) (W : Hilbert I →L[ℂ] Hilbert I) :
    Gt rho sigma t W ≤ Qv e f r s t - 1 / (1 + t) := by
  have hle := val_le e f hr0 hs0 hr1 hs1 ht ((((1 + t)⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + W)
  rw [val_shift rho sigma e f r s hr0 hr1 hev hs0 hs1 hfv ht] at hle
  rw [one_div]
  linarith

/-! ### P2l: G_t of the compressions P_s W P_s converges to G_t(W). -/

/-- The compression P_s W P_s. -/
def Wc (s : Finset I) (W : Hilbert I →L[ℂ] Hilbert I) : Hilbert I →L[ℂ] Hilbert I :=
  (Ps s).comp (W.comp (Ps s))

lemma Wc_apply (s : Finset I) (W : Hilbert I →L[ℂ] Hilbert I) (x : Hilbert I) :
    Wc s W x = Ps s (W (Ps s x)) := rfl

lemma Wc_norm (s : Finset I) (W : Hilbert I →L[ℂ] Hilbert I) (x : Hilbert I) :
    ‖Wc s W x‖ ≤ ‖W‖ * ‖x‖ :=
  (Ps_norm s _).trans ((W.le_opNorm _).trans (mul_le_mul_of_nonneg_left (Ps_norm s x) (norm_nonneg _)))

lemma Wc_adj (s : Finset I) (W : Hilbert I →L[ℂ] Hilbert I) :
    ContinuousLinearMap.adjoint (Wc s W) = Wc s (ContinuousLinearMap.adjoint W) := by
  simp only [Wc, ContinuousLinearMap.adjoint_comp, Ps_adj, ContinuousLinearMap.comp_assoc]

lemma tannery_inner {ι : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (r : ι → ℝ) (hr0 : ∀ i, 0 ≤ r i)
    (hr1 : Summable r) (W : Hilbert I →L[ℂ] Hilbert I) :
    Filter.Tendsto (fun s : Finset I => ∑' i, (r i : ℂ) * ⟪e i, Wc s W (e i)⟫_ℂ) Filter.atTop
      (nhds (∑' i, (r i : ℂ) * ⟪e i, W (e i)⟫_ℂ)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun i => r i * ‖W‖) (hr1.mul_right _)
    (fun i => ?_) (Filter.Eventually.of_forall fun s i => ?_)
  · exact ((tendsto_const_nhds.inner (PWP_tendsto W (e i))).const_mul _)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 i)]
    refine mul_le_mul_of_nonneg_left ?_ (hr0 i)
    refine (norm_inner_le_norm _ _).trans ?_
    rw [e.orthonormal.1 i, one_mul]
    have := Wc_norm s W (e i)
    rwa [e.orthonormal.1 i, mul_one] at this

lemma tannery_sq {ι : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (r : ι → ℝ) (hr0 : ∀ i, 0 ≤ r i)
    (hr1 : Summable r) (W : Hilbert I →L[ℂ] Hilbert I) :
    Filter.Tendsto (fun s : Finset I => ∑' i, r i * ‖Wc s W (e i)‖ ^ 2) Filter.atTop
      (nhds (∑' i, r i * ‖W (e i)‖ ^ 2)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun i => r i * ‖W‖ ^ 2) (hr1.mul_right _)
    (fun i => ?_) (Filter.Eventually.of_forall fun s i => ?_)
  · exact (((PWP_tendsto W (e i)).norm.pow 2).const_mul _)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hr0 i) (sq_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (hr0 i)
    have := Wc_norm s W (e i)
    rw [e.orthonormal.1 i, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2

/-- P2l: G_t(P_s W P_s) → G_t(W) along finite sets. -/
theorem Gt_tendsto (rho sigma : State I) (t : ℝ) (W : Hilbert I →L[ℂ] Hilbert I) :
    Filter.Tendsto (fun s : Finset I => Gt rho sigma t (Wc s W)) Filter.atTop
      (nhds (Gt rho sigma t W)) := by
  obtain ⟨ι, e, r, hr0, hr1, hev⟩ := state_eigen rho
  obtain ⟨κ, f, q, hq0, hq1, hfv⟩ := state_eigen sigma
  have hA : ∀ V : Hilbert I →L[ℂ] Hilbert I, boundedTracePair rho.coefficients V =
      ∑' i, (r i : ℂ) * ⟪e i, V (e i)⟫_ℂ := fun V =>
    (pair_eigen rho e r hr0 hr1.summable hev V).tsum_eq.symm
  have hB : ∀ V : Hilbert I →L[ℂ] Hilbert I, boundedTracePair sigma.coefficients V =
      ∑' j, (q j : ℂ) * ⟪f j, V (f j)⟫_ℂ := fun V =>
    (pair_eigen sigma f q hq0 hq1.summable hfv V).tsum_eq.symm
  have hA2 : ∀ V : Hilbert I →L[ℂ] Hilbert I,
      (boundedTracePair rho.coefficients ((ContinuousLinearMap.adjoint V).comp V)).re =
      ∑' i, r i * ‖V (e i)‖ ^ 2 := fun V =>
    (pair_eigen_sq rho e r hr0 hr1.summable hev V).tsum_eq.symm
  have hB2 : ∀ V : Hilbert I →L[ℂ] Hilbert I,
      (boundedTracePair sigma.coefficients (V.comp (ContinuousLinearMap.adjoint V))).re =
      ∑' j, q j * ‖(ContinuousLinearMap.adjoint V) (f j)‖ ^ 2 := by
    intro V
    have h := (pair_eigen_sq sigma f q hq0 hq1.summable hfv (ContinuousLinearMap.adjoint V)).tsum_eq.symm
    rwa [ContinuousLinearMap.adjoint_adjoint] at h
  have e1 : (fun s : Finset I => Gt rho sigma t (Wc s W)) = fun s =>
      2 / (1 + t) * ((∑' i, (r i : ℂ) * ⟪e i, Wc s W (e i)⟫_ℂ) -
        ∑' j, (q j : ℂ) * ⟪f j, Wc s W (f j)⟫_ℂ).re
      - ∑' j, q j * ‖Wc s (ContinuousLinearMap.adjoint W) (f j)‖ ^ 2
      - t * ∑' i, r i * ‖Wc s W (e i)‖ ^ 2 := by
    funext s
    unfold Gt
    rw [hA, hB, hA2, hB2, Wc_adj]
  have e2 : Gt rho sigma t W =
      2 / (1 + t) * ((∑' i, (r i : ℂ) * ⟪e i, W (e i)⟫_ℂ) -
        ∑' j, (q j : ℂ) * ⟪f j, W (f j)⟫_ℂ).re
      - ∑' j, q j * ‖(ContinuousLinearMap.adjoint W) (f j)‖ ^ 2
      - t * ∑' i, r i * ‖W (e i)‖ ^ 2 := by
    unfold Gt
    rw [hA, hB, hA2, hB2]
  rw [e1, e2]
  refine ((((Complex.continuous_re.tendsto _).comp ((tannery_inner e r hr0 hr1.summable W).sub
    (tannery_inner f q hq0 hq1.summable W))).const_mul _).sub
    (tannery_sq f q hq0 hq1.summable _)).sub ((tannery_sq e r hr0 hr1.summable W).const_mul _)

/-! ### P2e: the compression in matrix coordinates. -/

/-- The block of B on s: blk i j = <δ_i, B δ_j>. -/
def blk (s : Finset I) (B : Hilbert I →L[ℂ] Hilbert I) : Matrix s s ℂ :=
  fun i j => ⟪stdB I i, B (stdB I j)⟫_ℂ

/-- The compression of a coefficient array to s. -/
def cmp (s : Finset I) (X : Matrix I I ℂ) : Matrix s s ℂ :=
  X.submatrix (fun i : s => i.val) (fun i : s => i.val)

lemma coord (y : Hilbert I) (k : I) : ⟪stdB I k, y⟫_ℂ = y k := by
  rw [stdB_apply, bvec, lp.inner_single_left]; simp

lemma bO_coord (rho : State I) (l k : I) :
    ⟪stdB I l, boundedOperator rho.coefficients (stdB I k)⟫_ℂ = rho.coefficients l k := by
  rw [coord, stdB_apply]
  have := congrFun (congrFun (coeff_bO rho.density.1) l) k
  rw [← this, operatorCoeff_apply]; rfl

theorem L_blk (rho : State I) (s : Finset I) (B : Hilbert I →L[ℂ] Hilbert I) :
    boundedTracePair rho.coefficients (Wc s B) = (cmp s rho.coefficients * blk s B).trace := by
  unfold boundedTracePair
  have hterm : ∀ k, operatorCoeff ((Wc s B).comp (boundedOperator rho.coefficients)) k k =
      if k ∈ s then ∑ l ∈ s, rho.coefficients l k * ⟪stdB I k, B (stdB I l)⟫_ℂ else 0 := by
    intro k
    rw [operatorCoeff_apply, ← coord, show (lp.single 2 k (1:ℂ) : Hilbert I) = stdB I k from (stdB_apply k).symm,
      ContinuousLinearMap.comp_apply, Wc_apply, inner_Ps]
    split_ifs with hk
    · rw [Ps_apply, map_sum, inner_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, inner_smul_right, bO_coord]
    · rfl
  simp_rw [hterm]
  rw [tsum_eq_sum (s := s) (fun k hk => if_neg hk), Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, cmp, blk, Matrix.submatrix_apply]
  rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [if_pos k.2, ← Finset.sum_coe_sort s]


lemma Wc_mul (s : Finset I) (W X : Hilbert I →L[ℂ] Hilbert I) :
    (Wc s W).comp (Wc s X) = Wc s (W.comp ((Ps s).comp X)) := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, Wc_apply, Ps_idem]

lemma blk_mul (s : Finset I) (W X : Hilbert I →L[ℂ] Hilbert I) :
    blk s (W.comp ((Ps s).comp X)) = blk s W * blk s X := by
  ext i j
  simp only [blk, Matrix.mul_apply, ContinuousLinearMap.comp_apply, Ps_apply, map_sum, map_smul,
    inner_sum, inner_smul_right]
  rw [← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma blk_adj (s : Finset I) (W : Hilbert I →L[ℂ] Hilbert I) :
    blk s (ContinuousLinearMap.adjoint W) = (blk s W)ᴴ := by
  ext i j
  simp only [blk, Matrix.conjTranspose_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_conj_symm]; rfl

/-- P2e: G_t of a compression is the finite functional of the block. -/
theorem Gt_blk (rho sigma : State I) (t : ℝ) (s : Finset I) (W : Hilbert I →L[ℂ] Hilbert I) :
    Gt rho sigma t (Wc s W) =
      P45C4E.gfin (cmp s rho.coefficients) (cmp s sigma.coefficients) t (blk s W) := by
  unfold Gt P45C4E.gfin
  simp only [Wc_adj, Wc_mul, L_blk, blk_mul, blk_adj, Matrix.mul_assoc, Matrix.sub_mul, Matrix.trace_sub]

/-- Every block is realised by a bounded operator. -/
def extM (s : Finset I) (V : Matrix s s ℂ) : Hilbert I →L[ℂ] Hilbert I :=
  ∑ i : s, ∑ j : s, V i j • InnerProductSpace.rankOne ℂ (stdB I i) (stdB I j)

lemma blk_ext (s : Finset I) (V : Matrix s s ℂ) : blk s (extM s V) = V := by
  ext a b
  simp only [blk, extM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp (stdB I).orthonormal, Subtype.coe_inj]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma cmp_psd (rho : State I) (s : Finset I) : (cmp s rho.coefficients).PosSemidef := by
  have hM : PSDForms rho.coefficients := rho.density.2.1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    simp only [cmp, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
    exact (psd_herm hM b.val a.val).symm
  · intro x
    set z : I → ℂ := fun j => if h : j ∈ s then x ⟨j, h⟩ else 0
    have e : star x ⬝ᵥ ((cmp s rho.coefficients) *ᵥ x) =
        ∑ i ∈ s, ∑ j ∈ s, star (z i) * rho.coefficients i j * z j := by
      simp only [cmp, dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Finset.mul_sum]
      rw [← Finset.sum_coe_sort s]
      apply Finset.sum_congr rfl; intro a _
      rw [← Finset.sum_coe_sort s]
      apply Finset.sum_congr rfl; intro b _
      simp only [z, a.2, b.2, dif_pos, Pi.star_apply, Subtype.coe_eta]; ring
    rw [e]
    have h := hM s z
    exact Complex.le_def.mpr ⟨by simpa using h.2, by simpa using h.1.symm⟩

/-- The finite integrand of the compressions, jfin_s(t). -/
def jS (rho sigma : State I) (s : Finset I) (t : ℝ) : ℝ :=
  P45C4E.jfin (cmp_psd rho s).isHermitian (cmp_psd sigma s).isHermitian t

theorem jS_le (rho sigma : State I) {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I))
    (f : HilbertBasis κ ℂ (Hilbert I)) (r : ι → ℝ) (q : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : Summable q)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (q j : ℂ) • f j)
    {t : ℝ} (ht : 0 < t) (s : Finset I) :
    jS rho sigma s t ≤ Qv e f r q t - 1 / (1 + t) := by
  unfold jS
  rw [← P45C4E.gfin_opt _ _ ht (cmp_psd rho s).eigenvalues_nonneg (cmp_psd sigma s).eigenvalues_nonneg,
    ← blk_ext s (_ * _ * _), ← Gt_blk]
  exact Gt_le rho sigma e f r q hr0 hr1 hev hq0 hq1 hfv ht _

theorem Gt_le_jS (rho sigma : State I) {t : ℝ} (ht : 0 < t) (s : Finset I) (W : Hilbert I →L[ℂ] Hilbert I) :
    Gt rho sigma t (Wc s W) ≤ jS rho sigma s t := by
  rw [Gt_blk]
  exact P45C4E.gfin_le _ _ ht (cmp_psd rho s).eigenvalues_nonneg (cmp_psd sigma s).eigenvalues_nonneg _

/-- jfin_s(t) → J_t = Q_t - 1/(1+t) along finite sets. -/
theorem jS_tendsto (rho sigma : State I) {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I))
    (f : HilbertBasis κ ℂ (Hilbert I)) (r : ι → ℝ) (q : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : Summable q)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (q j : ℂ) • f j)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun s => jS rho sigma s t) Filter.atTop (nhds (Qv e f r q t - 1 / (1 + t))) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => Filter.Eventually.of_forall fun s =>
    (jS_le rho sigma e f r q hr0 hr1 hev hq0 hq1 hfv ht s).trans_lt hb⟩
  have hT := val_trunc_tendsto e f hr0 hq0 hr1 hq1 ht
  have h1 : a + 1 / (1 + t) < Qv e f r q t := by linarith
  obtain ⟨F, hF⟩ := (hT.eventually (lt_mem_nhds h1)).exists
  set W := truncOp e f r q t F - (((1 + t)⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) with hW
  have hv := val_shift rho sigma e f r q hr0 hr1 hev hq0 hq1 hfv ht W
  have hW' : (((1 + t)⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (Hilbert I) + W = truncOp e f r q t F := by
    rw [hW]; abel
  rw [hW'] at hv
  have hGa : a < Gt rho sigma t W := by rw [one_div] at hF; linarith
  filter_upwards [(Gt_tendsto rho sigma t W).eventually (lt_mem_nhds hGa)] with s hs
  exact hs.trans_le (Gt_le_jS rho sigma ht s W)


open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy extendedRelativeEntropyNats) in
open MeasureTheory Set in
/-- K-b: for states with finite relative entropy, D(rho||sigma) = Int_{t>0} (Q_t - 1/(1+t)) dt. -/
theorem kb_integral [Countable I] (rho sigma : State I) {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I))
    (f : HilbertBasis κ ℂ (Hilbert I)) (r : ι → ℝ) (q : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : Summable q)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (q j : ℂ) • f j)
    (hD : extendedRelativeEntropyNats rho.coefficients sigma.coefficients < ⊤) :
    extendedRelativeEntropyNats rho.coefficients sigma.coefficients =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Qv e f r q t - 1 / (1 + t)) := by
  have hfin : ∀ s : Finset I, finiteRelativeEntropy (cmp s rho.coefficients) (cmp s sigma.coefficients) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (jS rho sigma s t) := by
    intro s
    have hlt : finiteRelativeEntropy (cmp s rho.coefficients) (cmp s sigma.coefficients) < ⊤ :=
      lt_of_le_of_lt (le_iSup (fun s : Finset I => finiteRelativeEntropy (cmp s rho.coefficients)
        (cmp s sigma.coefficients)) s) hD
    have hker : LinearMap.ker (cmp s sigma.coefficients).mulVecLin ≤
        LinearMap.ker (cmp s rho.coefficients).mulVecLin := by
      by_contra h
      rw [finiteRelativeEntropy, if_neg h] at hlt
      exact lt_irrefl _ hlt
    exact P45C4E.fre_lint (cmp_psd rho s) (cmp_psd sigma s) hker
  have hD' : extendedRelativeEntropyNats rho.coefficients sigma.coefficients =
      ⨆ s : Finset I, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (jS rho sigma s t) :=
    iSup_congr hfin
  rw [hD']
  refine le_antisymm (iSup_le fun s => setLIntegral_mono' measurableSet_Ioi fun t ht =>
    ENNReal.ofReal_le_ofReal (jS_le rho sigma e f r q hr0 hr1 hev hq0 hq1 hfv ht s)) ?_
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset I))
  have hmeas : ∀ s, Measurable fun t => ENNReal.ofReal (jS rho sigma s t) := by
    intro s
    unfold jS P45C4E.jfin
    exact Measurable.ennreal_ofReal (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (P45C4D.kbK_meas _ _).const_mul _)
  calc ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (Qv e f r q t - 1 / (1 + t))
      = ∫⁻ t in Ioi (0:ℝ), Filter.liminf (fun n => ENNReal.ofReal (jS rho sigma (u n) t)) Filter.atTop := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        exact ((ENNReal.tendsto_ofReal ((jS_tendsto rho sigma e f r q hr0 hr1 hev hq0 hq1 hfv
          ht).comp hu)).liminf_eq).symm
    _ ≤ Filter.liminf (fun n => ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (jS rho sigma (u n) t)) Filter.atTop :=
        lintegral_liminf_le fun n => hmeas (u n)
    _ ≤ ⨆ n, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (jS rho sigma (u n) t) :=
        le_trans Filter.liminf_le_limsup Filter.limsup_le_iSup
    _ ≤ ⨆ s : Finset I, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (jS rho sigma s t) :=
        iSup_le fun n => le_iSup (fun s : Finset I => ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (jS rho sigma s t)) (u n)


end P45C4F

end

end C4fPart


/-! ## C4 K-d (s15): equality of relative entropies forces Q_t(out) = Q_t(in) for every t > 0.
Iteration file: imports the laptop-built olean P45S.C4f. -/
section C4gPart

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

namespace P45C4G

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy extendedRelativeEntropyNats)
open P45Petz P45C4 P45C4B P45C4F
open MeasureTheory Set

variable {I J : Type}

/-- Q_t is continuous on (a, ∞) for a > 0 (uniform domination by |c_p|^2 r_i / a). -/
lemma Qv_contOn {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (q : κ → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r) (hq0 : ∀ j, 0 ≤ q j)
    {a : ℝ} (ha : 0 < a) : ContinuousOn (fun t => Qv e f r q t) (Ioi a) := by
  have hS := P45C4D.cA_hasSum e f r hr0 hr1.hasSum
  refine continuousOn_tsum (u := fun p : κ × ι => ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 / a)
    (fun p => ?_) (hS.summable.div_const a) (fun p t ht => ?_)
  · rcases (hr0 p.2).lt_or_eq with hpos | hzero
    · refine ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_id.mul continuousOn_const)) (fun t ht => ?_)
      have ht0 : 0 < t := lt_trans ha ht
      exact (add_pos_of_nonneg_of_pos (hq0 _) (mul_pos ht0 hpos)).ne'
    · simp only [← hzero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div]
      exact continuousOn_const
  · have ht0 : 0 < t := lt_trans ha ht
    have hc := sq_nonneg ‖⟪f p.1, e p.2⟫_ℂ‖
    rcases (hr0 p.2).lt_or_eq with hpos | hzero
    · have hd : 0 < q p.1 + t * r p.2 := add_pos_of_nonneg_of_pos (hq0 _) (mul_pos ht0 hpos)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hc (sq_nonneg _)) hd.le),
        div_le_div_iff₀ hd ha]
      have h1 : r p.2 * a ≤ q p.1 + t * r p.2 := by
        nlinarith [hq0 p.1, mul_le_mul_of_nonneg_left (le_of_lt (show a < t from ht)) (hr0 p.2)]
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc (hr0 p.2))
      nlinarith [h2]
    · rw [← hzero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
        norm_zero, le_refl]

lemma Qv_contOn0 {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (q : κ → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r) (hq0 : ∀ j, 0 ≤ q j) :
    ContinuousOn (fun t => Qv e f r q t - 1 / (1 + t)) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hQ : ContinuousAt (fun t => Qv e f r q t) t :=
    (Qv_contOn e f r q hr0 hr1 hq0 (half_pos ht0)).continuousAt
      (Ioi_mem_nhds (half_lt_self ht0))
  have hR : ContinuousAt (fun t : ℝ => 1 / (1 + t)) t :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith)
  exact (hQ.sub hR).continuousWithinAt

/-- J_t = Q_t - 1/(1+t) ≥ 0 for states. -/
lemma J_nonneg (rho sigma : State I) {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I))
    (f : HilbertBasis κ ℂ (Hilbert I)) (r : ι → ℝ) (q : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : Summable q)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (q j : ℂ) • f j)
    {t : ℝ} (ht : 0 < t) : 0 ≤ Qv e f r q t - 1 / (1 + t) := by
  refine ge_of_tendsto' (jS_tendsto rho sigma e f r q hr0 hr1 hev hq0 hq1 hfv ht) fun s => ?_
  unfold jS P45C4E.jfin
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _)
    (P45C4D.kbK_nonneg' ((cmp_psd rho s).eigenvalues_nonneg i)
      ((cmp_psd sigma s).eigenvalues_nonneg j) ht)

/-- K-d: if D(Phi rho||Phi sigma) = D(rho||sigma) < ⊤ then Q_t(out) = Q_t(in) for all t > 0. -/
theorem kd [Countable I] [Countable J] (Phi : Channel I J) (rho sigma : State I)
    {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr1' : Summable r0)
    (hev' : ∀ i, boundedOperator (Phi.val rho.coefficients) (e0 i) = (r0 i : ℂ) • e0 i)
    (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (hfv' : ∀ j, boundedOperator (Phi.val sigma.coefficients) (f0 j) = (s0 j : ℂ) • f0 j)
    (hD : extendedRelativeEntropyNats rho.coefficients sigma.coefficients < ⊤)
    (heq : extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val sigma.coefficients) =
      extendedRelativeEntropyNats rho.coefficients sigma.coefficients) :
    ∀ t, 0 < t → Qv e0 f0 r0 s0 t = Qv e f r s t := by
  set rho' : State J := ⟨_, chan_density Phi.val Phi.property _ rho.density⟩
  set sigma' : State J := ⟨_, chan_density Phi.val Phi.property _ sigma.density⟩
  have hin := kb_integral rho sigma e f r s hr0 hr1 hev hs0 hs1 hfv hD
  have hout := kb_integral rho' sigma' e0 f0 r0 s0 hr0' hr1' hev' hs0' hs1' hfv' (heq ▸ hD)
  have hle : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (Qv e0 f0 r0 s0 t - 1 / (1 + t)) ≤
      ENNReal.ofReal (Qv e f r s t - 1 / (1 + t)) := fun t ht =>
    ENNReal.ofReal_le_ofReal (sub_le_sub_right (P45C4C.Q_mono Phi rho sigma e f r s hr0 hr1 hev hs0 hs1
      hfv e0 f0 r0 s0 hr0' hr1' hev' hs0' hs1' hfv' t ht) _)
  have hcin := Qv_contOn0 e f r s hr0 hr1 hs0
  have hcout := Qv_contOn0 e0 f0 r0 s0 hr0' hr1' hs0'
  have hae : (fun t => ENNReal.ofReal (Qv e0 f0 r0 s0 t - 1 / (1 + t))) =ᵐ[volume.restrict (Ioi 0)]
      fun t => ENNReal.ofReal (Qv e f r s t - 1 / (1 + t)) := by
    refine ae_eq_of_ae_le_of_lintegral_le ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall hle)) ?_
      ((ENNReal.continuous_ofReal.comp_continuousOn hcin).aemeasurable measurableSet_Ioi) ?_
    · have : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Qv e0 f0 r0 s0 t - 1 / (1 + t)) < ⊤ := by
        rw [← hout]; exact heq ▸ hD
      exact this.ne
    · rw [← hin, ← hout]; exact heq.ge
  have heqOn := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
    (ENNReal.continuous_ofReal.comp_continuousOn hcout) (ENNReal.continuous_ofReal.comp_continuousOn hcin)
  intro t ht
  have h1 := heqOn ht
  simp only [Function.comp_apply] at h1
  rw [ENNReal.ofReal_eq_ofReal_iff (J_nonneg rho' sigma' e0 f0 r0 s0 hr0' hr1' hev' hs0' hs1' hfv' ht)
    (J_nonneg rho sigma e f r s hr0 hr1 hev hs0 hs1 hfv ht)] at h1
  linarith

end P45C4G

end

end C4gPart

section C4iPart

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

namespace P45C4I

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy extendedRelativeEntropyNats)
open P45Petz P45C4 P45C4B P45C4C P45C4F P45C4G
open MeasureTheory Set Filter Topology

variable {I J : Type}

lemma Qv_term_le {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (q : κ → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hq0 : ∀ j, 0 ≤ q j) {t : ℝ} (ht : 0 < t)
    (p : κ × ι) :
    0 ≤ ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 / (q p.1 + t * r p.2) ∧
    ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 / (q p.1 + t * r p.2) ≤
      ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 / t := by
  have hc := sq_nonneg ‖⟪f p.1, e p.2⟫_ℂ‖
  rcases (hr0 p.2).lt_or_eq with hpos | hzero
  · have hd : 0 < q p.1 + t * r p.2 := add_pos_of_nonneg_of_pos (hq0 _) (mul_pos ht hpos)
    refine ⟨div_nonneg (mul_nonneg hc (sq_nonneg _)) hd.le, ?_⟩
    rw [div_le_div_iff₀ hd ht]
    have h1 : r p.2 * t ≤ q p.1 + t * r p.2 := by nlinarith [hq0 p.1]
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc (hr0 p.2))
    nlinarith [h2]
  · rw [← hzero]
    simp

lemma Qv_summable {ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (q : κ → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r) (hq0 : ∀ j, 0 ≤ q j)
    {t : ℝ} (ht : 0 < t) :
    Summable fun p : κ × ι => ‖⟪f p.1, e p.2⟫_ℂ‖ ^ 2 * r p.2 ^ 2 / (q p.1 + t * r p.2) :=
  Summable.of_nonneg_of_le (fun p => (Qv_term_le e f r q hr0 hq0 ht p).1)
    (fun p => (Qv_term_le e f r q hr0 hq0 ht p).2)
    ((P45C4D.cA_hasSum e f r hr0 hr1.hasSum).summable.div_const t)

lemma lint_inv_top {b : ℝ} (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioc (0 : ℝ) b, ENNReal.ofReal (c * t⁻¹) = ⊤ := by
  have hm : Measurable fun t : ℝ => ENNReal.ofReal t⁻¹ := measurable_inv.ennreal_ofReal
  have h1 : ∫⁻ t in Ioc (0 : ℝ) b, ENNReal.ofReal t⁻¹ = ⊤ := by
    by_contra hne
    have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc 0 b) := by
      refine ⟨measurable_inv.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal]
      · exact lt_top_iff_ne_top.mpr hne
      · exact (ae_restrict_iff' measurableSet_Ioc).mpr
          (Eventually.of_forall fun t ht => inv_nonneg.mpr ht.1.le)
    have hii : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr hint
    rw [intervalIntegrable_inv_iff] at hii
    rcases hii with h | h
    · exact hb.ne h
    · exact h (Set.left_mem_uIcc)
  have h2 : (fun t : ℝ => ENNReal.ofReal (c * t⁻¹)) =
      fun t => ENNReal.ofReal c * ENNReal.ofReal t⁻¹ := by
    funext t; exact ENNReal.ofReal_mul hc.le
  rw [h2, lintegral_const_mul _ hm, h1]
  exact ENNReal.mul_top (by simpa using hc)

/-- Support lemma: D(rho||sigma) < ⊤ forces ⟪f j, e i⟫ = 0 whenever q j = 0 < r i. -/
theorem supp_of_D [Countable I] (rho sigma : State I) {ι κ : Type}
    (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I)) (r : ι → ℝ) (q : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : Summable q)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (q j : ℂ) • f j)
    (hD : extendedRelativeEntropyNats rho.coefficients sigma.coefficients < ⊤) :
    ∀ j i, q j = 0 → 0 < r i → ⟪f j, e i⟫_ℂ = 0 := by
  intro j i hqj hri
  by_contra hc
  set a : ℝ := ‖⟪f j, e i⟫_ℂ‖ ^ 2 * r i with ha_def
  have ha : 0 < a := mul_pos (pow_pos (norm_pos_iff.mpr hc) 2) hri
  have hb : 0 < a / 2 := half_pos ha
  have hbound : ∀ t ∈ Ioc (0 : ℝ) (a / 2),
      ENNReal.ofReal (a / 2 * t⁻¹) ≤ ENNReal.ofReal (Qv e f r q t - 1 / (1 + t)) := by
    intro t ht
    refine ENNReal.ofReal_le_ofReal ?_
    have ht0 : 0 < t := ht.1
    have hterm : a / t ≤ Qv e f r q t := by
      have hle := (Qv_summable e f r q hr0 hr1 hq0 ht0).le_tsum (j, i)
        (fun p _ => (Qv_term_le e f r q hr0 hq0 ht0 p).1)
      unfold Qv
      refine le_trans (le_of_eq ?_) hle
      simp only [hqj, zero_add, ha_def]
      field_simp
    have h1 : 1 / (1 + t) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have h2 : 1 ≤ a / 2 * t⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ ht0]; linarith [ht.2]
    have h3 : a / t = a / 2 * t⁻¹ + a / 2 * t⁻¹ := by ring
    linarith
  have hlt := hD
  rw [kb_integral rho sigma e f r q hr0 hr1 hev hq0 hq1 hfv hD] at hlt
  have : (⊤ : ENNReal) ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Qv e f r q t - 1 / (1 + t)) :=
    calc (⊤ : ENNReal) = ∫⁻ t in Ioc (0 : ℝ) (a / 2), ENNReal.ofReal (a / 2 * t⁻¹) :=
          (lint_inv_top hb hb).symm
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) (a / 2), ENNReal.ofReal (Qv e f r q t - 1 / (1 + t)) :=
          setLIntegral_mono' measurableSet_Ioc hbound
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Qv e f r q t - 1 / (1 + t)) :=
          lintegral_mono_set Ioc_subset_Ioi_self
  exact absurd (top_le_iff.mp this) hlt.ne

end P45C4I

end

end C4iPart

section ChildRoot

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

/-! The shortcut instances above are global; erase them here so the statement below elaborates with the
    standard instance terms (the platform binder-structure gate compares the elaborated statement). -/
attribute [-instance] P45Petz.gfc0 P45Petz.gfc1 P45Petz.gfc2 P45Petz.gfc3 P45Petz.gfc4 P45Petz.gfc5
attribute [-instance] P45Petz.gfc6 P45Petz.gfc7 P45Petz.gsc0 P45Petz.gsc1 P45Petz.gsc2 P45Petz.gsc3
attribute [-instance] P45Petz.gsc4 P45Petz.gsc5 P45Petz.gsc6 P45Petz.gsc7 P45Petz.gsc8 P45Petz.gsc9
attribute [-instance] P45Petz.gsc10 P45Petz.gsc11 P45Petz.gsc12 P45Petz.gsc13 P45Petz.gsc14 P45Petz.gsc15
attribute [-instance] P45Petz.gsc16 P45Petz.gsc17 P45Petz.gsc18 P45Petz.gsc19 P45Petz.gsc20 P45Petz.gsc21
attribute [-instance] P45Petz.gsc22 P45Petz.gsc23 P45Petz.gsc24 P45Petz.gsc25 P45Petz.gsc26 P45Petz.gsc27
attribute [-instance] P45Petz.gsc28 P45Petz.hsc0 P45Petz.hsc1 P45Petz.hsc2 P45Petz.hsc3 P45Petz.hsc4
attribute [-instance] P45Petz.hsc5 P45Petz.hsc6 P45Petz.hsc7 P45Petz.hsc8 P45Petz.hsc9 P45Petz.hsc10
attribute [-instance] P45Petz.hsc11 P45Petz.hsc12 P45Petz.hsc13 P45Petz.hsc14 P45Petz.hsc15 P45Petz.hsc16
attribute [-instance] P45Petz.hsc17 P45Petz.hsc18 P45Petz.hsc19 P45Petz.hsc20 P45Petz.hsc21 P45Petz.hsc22
attribute [-instance] P45Petz.hsc23 P45Petz.hsc24 P45Petz.hsc25 P45Petz.hsc26 P45Petz.hsc27 P45Petz.hsc28
attribute [-instance] P45Petz.hsc29

open QAlgorithms.Papers.Independent.Gap48.P45 QAlgorithms.RealRegisters QAlgorithms.Papers.Independent.Dependency50.P33 QAlgorithms.Papers.Independent.Frontier18.P01 QAlgorithms.Papers.Independent.Frontier18.P07 QAlgorithms.Papers.Independent.Frontier18.P18 in
theorem solution
    {I J : Type} [Countable I] [Countable J]
    (Phi : Channel I J) (rho sigma : State I)
    {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr1' : Summable r0)
    (hev' : ∀ i, boundedOperator (Phi.val rho.coefficients) (e0 i) = (r0 i : ℂ) • e0 i)
    (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (hfv' : ∀ j, boundedOperator (Phi.val sigma.coefficients) (f0 j) = (s0 j : ℂ) • f0 j)
    (hD : extendedRelativeEntropyNats rho.coefficients sigma.coefficients < ⊤)
    (heq : extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val sigma.coefficients) =
      extendedRelativeEntropyNats rho.coefficients sigma.coefficients) :
    (∀ t : ℝ, 0 < t →
      ∑' p : κ0 × ι0, ‖inner ℂ (f0 p.1) (e0 p.2)‖ ^ 2 * r0 p.2 ^ 2 / (s0 p.1 + t * r0 p.2) =
        ∑' p : κ × ι, ‖inner ℂ (f p.1) (e p.2)‖ ^ 2 * r p.2 ^ 2 / (s p.1 + t * r p.2)) ∧
    (∀ j i, s j = 0 → 0 < r i → inner ℂ (f j) (e i) = 0) ∧
    (∀ j i, s0 j = 0 → 0 < r0 i → inner ℂ (f0 j) (e0 i) = 0) := by
  refine ⟨P45C4G.kd Phi rho sigma e f r s hr0 hr1 hev hs0 hs1 hfv e0 f0 r0 s0 hr0' hr1' hev' hs0' hs1' hfv'
    hD heq, P45C4I.supp_of_D rho sigma e f r s hr0 hr1 hev hs0 hs1 hfv hD, ?_⟩
  exact P45C4I.supp_of_D (⟨_, P45Petz.chan_density Phi.val Phi.property _ rho.density⟩ : State J)
    (⟨_, P45Petz.chan_density Phi.val Phi.property _ sigma.density⟩ : State J)
    e0 f0 r0 s0 hr0' hr1' hev' hs0' hs1' hfv' (heq ▸ hD)

end

end ChildRoot
