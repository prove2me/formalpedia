-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.petz_threeConditions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T03:20:11.061922+00:00
-- url     : https://prove2.me/submissions/a1d64212-06f7-4275-a1a1-97510763e683

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
import Definitions.Def_SimpleSSA_Monotone_Basic
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petzRecovery_isChannel_and_recovers_sigma
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_extendedRelativeEntropy_monotone_of_finite_ssa
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_equality_resolvent_and_supports
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_equality_approximate_intertwiner
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_equality_matrix_entries
import Theorems.Thm_SimpleSSA_Monotone_eq_4

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


/-! Shortcut instances on operators (speed). -/
instance (priority := 10000) osc0 (T : Type) : Ring (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc1 (T : Type) : Semiring (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc2 (T : Type) : NormedRing (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc3 (T : Type) : Algebra ℂ (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc4 (T : Type) : NormedAlgebra ℂ (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc5 (T : Type) : StarRing (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc6 (T : Type) : CStarRing (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc7 (T : Type) : StarModule ℂ (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc8 (T : Type) : PartialOrder (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc9 (T : Type) : StarOrderedRing (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc10 (T : Type) : Module ℂ (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc11 (T : Type) : NormedSpace ℂ (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc12 (T : Type) : AddCommGroup (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc13 (T : Type) : AddCommMonoid (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc14 (T : Type) : NormedAddCommGroup (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc15 (T : Type) : TopologicalSpace (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc16 (T : Type) : T2Space (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc17 (T : Type) : CompleteSpace (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc18 (T : Type) : Star (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc19 (T : Type) : Mul (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc20 (T : Type) : One (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc21 (T : Type) : SMul ℂ (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc22 (T : Type) : Monoid (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) osc23 (T : Type) : NonUnitalRing (Hilbert T →L[ℂ] Hilbert T) := inferInstance
instance (priority := 10000) hsc_t2 (T : Type) : T2Space (Hilbert T) := inferInstance
instance (priority := 10000) fsc0 (T U : Type) : FunLike (Hilbert T →L[ℂ] Hilbert U) (Hilbert T) (Hilbert U) := inferInstance
instance (priority := 10000) fsc1 (T U : Type) : ContinuousSemilinearMapClass (Hilbert T →L[ℂ] Hilbert U) (RingHom.id ℂ) (Hilbert T) (Hilbert U) := inferInstance
instance (priority := 10000) fsc2 (T U : Type) : AddMonoidHomClass (Hilbert T →L[ℂ] Hilbert U) (Hilbert T) (Hilbert U) := inferInstance
instance (priority := 10000) fsc3 (T U : Type) : AddCommGroup (Hilbert T →L[ℂ] Hilbert U) := inferInstance
instance (priority := 10000) fsc4 (T U : Type) : Module ℂ (Hilbert T →L[ℂ] Hilbert U) := inferInstance
instance (priority := 10000) fsc5 (T U : Type) : NormedAddCommGroup (Hilbert T →L[ℂ] Hilbert U) := inferInstance



/-! Helpers copied from scratch/probe/176d3efb_Aall.lean (P45D, compiled there). -/
lemma norm_coord_le {T : Type} (x : Hilbert T) (t : T) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by norm_num) x t

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
/-! ## Trace preservation on all of trace class -/

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

lemma unit_rk {I : Type} (i j : I) :
    boundedOperator (Matrix.single j i (1 : ℂ)) = rk (bvec j) (bvec i) := by
  apply bO_eq
  funext x y
  rw [coeff_rk]
  by_cases hx : x = j
  · subst hx
    by_cases hy : y = i
    · subst hy; simp [bvec, Matrix.single_apply]
    · simp [bvec, Matrix.single_apply, lp.single_apply, Pi.single_apply, Ne.symm hy, hy]
  · simp [bvec, Matrix.single_apply, lp.single_apply, Pi.single_apply, Ne.symm hx, hx]

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

/-! ## s3: uniqueness of the supported dual (U1) and D(I) = I (U2 part) -/

/-! ## s4 U5: a PSD matrix with summable diagonal is trace class -/

/-! ## s4: positivity of trace pairings -/

/-! ## s4 U3: complete positivity pieces -/

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

section Dual

variable {I J : Type}

/-! ### Duality Tr(Phi(X) W) = Tr(X Phi*(W)) on all trace class (normality via positive pieces) -/

end Dual

end P45C4B

end

end C4Bridge


/-! K-b scalar identity (s13): Int_0^inf (r-s)^2/((s+tr)(1+t)^2) dt = r log r - r log s + s - r (s > 0, r ≥ 0). -/

open MeasureTheory Set Filter Topology

namespace P45KB

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

variable {E ι κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

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

/-! ### P2f: finite-dimensional variational form of the Lindblad integrand. -/

section Var

variable {A B : Matrix F F ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)

end Var

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

/-! ### The trace pairing of a state as a linear functional. -/

/-! ### P2u: the shifted functional G_t is bounded by J_t = Q_t - 1/(1+t). -/

/-! ### P2l: G_t of the compressions P_s W P_s converges to G_t(W). -/

/-! ### P2e: the compression in matrix coordinates. -/

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

end P45C4G

end

end C4gPart


/-! ## C4 K-f analytic core (s16): uniqueness of the discrete Stieltjes transform.
If F(t) = Sum_m beta_m / (lam_m + t) vanishes for all t > 0 (lam >= 0, beta summable) then for
every x the atom mass Sum_{lam_m = x} beta_m is zero (analytic continuation to the slit plane
plus a residue limit at -x + i y, y -> 0+). Mathlib only. -/

set_option autoImplicit false

open Filter Topology Complex

noncomputable section

namespace P45STJ

variable {T : Type}

end P45STJ

end

/-! ## C4 K-e (s16): with equal Q_t, the dual images of the output optimiser truncations are
asymptotically optimal on the input side. Iteration file: imports the laptop-built olean P45S.C4g. -/
section C4hPart

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

namespace P45C4H

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy extendedRelativeEntropyNats)
open P45Petz P45C4 P45C4B P45C4C P45C4F P45C4G
open MeasureTheory Set Filter Topology

variable {I J : Type}

/-! ### K-f (s16): the pair vector of rho^{1/2} lies in the closure of the operator pairs
(sigma0^{1/2} Z, sigma^{1/2} Phi*(Z)), via the Hilbert closure and Stieltjes uniqueness. -/

section Pair

variable (Phi : Channel I J) {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I))
  (f : HilbertBasis κ ℂ (Hilbert I)) (s : κ → ℝ) (e0 : HilbertBasis ι0 ℂ (Hilbert J))
  (f0 : HilbertBasis κ0 ℂ (Hilbert J)) (s0 : κ0 → ℝ)

end Pair

section KF2

variable [Countable I] [Countable J]

end KF2


end P45C4H

end

end C4hPart


/-! ## C4 (s17): support lemma (finite relative entropy forces supp rho ≤ supp sigma in
eigencoordinates), then K-g. Iteration file: imports the laptop-built olean P45S.C4h. -/
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
open P45Petz P45C4 P45C4B P45C4C P45C4F P45C4G P45C4H
open MeasureTheory Set Filter Topology

variable {I J : Type}

/-! ### K-g building blocks (s17) -/

lemma bTP_rk {T : Type} (M : Matrix T T ℂ) (x y : Hilbert T) :
    boundedTracePair M (rk y x) = ⟪x, boundedOperator M y⟫_ℂ := by
  unfold boundedTracePair
  set P := boundedOperator M
  have h1 : ∀ l, operatorCoeff ((rk y x).comp P) l l =
      star ((ContinuousLinearMap.adjoint P x) l) * y l := by
    intro l
    rw [operatorCoeff_apply, ContinuousLinearMap.comp_apply, rk_apply]
    have h2 : star ((ContinuousLinearMap.adjoint P x) l) = ⟪x, P (lp.single 2 l 1)⟫_ℂ := by
      rw [coord_eq_inner, ContinuousLinearMap.adjoint_inner_right]
      show (starRingEnd ℂ) ⟪P (bvec l), x⟫_ℂ = _
      rw [inner_conj_symm]
      rfl
    rw [h2]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [tsum_congr h1, ← inner_eq_tsum', ContinuousLinearMap.adjoint_inner_left]

lemma psr_eig {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : E →L[ℂ] E) (hP : 0 ≤ P) (f : E) {s : ℝ} (hs : 0 ≤ s) (hf : P f = (s : ℂ) • f) :
    QAlgorithms.Papers.Independent.Next46.P31.positiveSquareRoot P f =
      ((Real.sqrt s : ℝ) : ℂ) • f := by
  obtain ⟨hsa, htt⟩ := psr_facts P hP
  have htpos : (QAlgorithms.Papers.Independent.Next46.P31.positiveSquareRoot P).IsPositive := by
    rw [psr_eq_sqrt P hP]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg P)
  set t := QAlgorithms.Papers.Independent.Next46.P31.positiveSquareRoot P with htdef
  have h1 : t (t f) = (s : ℂ) • f := by
    rw [← hf, ← htt]; rfl
  rcases hs.lt_or_eq with hpos | hzero
  · set c : ℂ := ((Real.sqrt s : ℝ) : ℂ) with hc
    set g := t f - c • f with hg
    have hcc : c * c = (s : ℂ) := by
      rw [hc, ← Complex.ofReal_mul, Real.mul_self_sqrt hs]
    have htg : t g = -(c • g) := by
      rw [hg, map_sub, map_smul, h1, smul_sub, smul_smul, hcc]
      abel
    have hre := pos_re htpos g
    rw [htg, inner_neg_left, inner_smul_left, inner_self_eq_norm_sq_to_K] at hre
    have hconj : (starRingEnd ℂ) c = c := by rw [hc, Complex.conj_ofReal]
    rw [hconj, hc] at hre
    have hre' : 0 ≤ -(Real.sqrt s * ‖g‖ ^ 2) := by
      have : (-(((Real.sqrt s : ℝ) : ℂ) * ((‖g‖ : ℂ) ^ 2))).re = -(Real.sqrt s * ‖g‖ ^ 2) := by
        simp [← Complex.ofReal_pow]
      linarith [this ▸ hre]
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hpos
    have hgn : ‖g‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖g‖]
    have hg0 : g = 0 := by
      have : ‖g‖ = 0 := by nlinarith [norm_nonneg g]
      exact norm_eq_zero.mp this
    exact sub_eq_zero.mp hg0
  · subst hzero
    have hn := sa_norm_sq hsa htt f
    rw [hf] at hn
    simp only [Complex.ofReal_zero, zero_smul, inner_zero_right, Complex.zero_re] at hn
    have : t f = 0 := by
      have h0 : ‖t f‖ = 0 := by nlinarith [norm_nonneg (t f)]
      exact norm_eq_zero.mp h0
    rw [this, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]

end P45C4I

end

end C4iPart


/-! ## C4 (s18): K-g. Coordinate maps lp(T) -> lp(ι, E) (continuous), pointwise operators on
lp(ι, E), trace identities, and MAIN: bTP(Phi rho, B) = bTP(rho, |u><v|) by the closed-set
argument at Rc. Iteration file: imports the laptop-built olean P45S.C4i. -/
section C4jPart

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

namespace P45C4J

open QAlgorithms.Papers.Independent.Gap48.P45
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsTraceClass IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy extendedRelativeEntropyNats)
open P45Petz P45C4 P45C4B P45C4C P45C4F P45C4G P45C4H P45C4I
open MeasureTheory Set Filter Topology

variable {I J : Type}

section Gen

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {T κ ι : Type} (f : HilbertBasis κ ℂ E) (π : ι × κ → T) (hπ : Function.Injective π)

include hπ

end Gen

section Pw

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type}

end Pw

/-! ### Trace identities -/

/-! ### MAIN (K-g) -/

section Main

variable [Countable I] [Countable J]

end Main

/-! ### Assembly of C4 -/

lemma supp_mem {T κ0 : Type} (X : Matrix T T ℂ) (f0 : HilbertBasis κ0 ℂ (Hilbert T)) (s0 : κ0 → ℝ)
    (hfv : ∀ j, boundedOperator X (f0 j) = (s0 j : ℂ) • f0 j) (x : Hilbert T)
    (hx : ∀ j, s0 j = 0 → ⟪f0 j, x⟫_ℂ = 0) :
    x ∈ (LinearMap.range (boundedOperator X).toLinearMap).topologicalClosure := by
  set K := (LinearMap.range (boundedOperator X).toLinearMap).topologicalClosure
  have hterm : ∀ j, f0.repr x j • f0 j ∈ K := by
    intro j
    by_cases h : s0 j = 0
    · rw [HilbertBasis.repr_apply_apply, hx j h, zero_smul]; exact K.zero_mem
    · apply Submodule.le_topologicalClosure
      refine ⟨(f0.repr x j / (s0 j : ℂ)) • f0 j, ?_⟩
      show boundedOperator X ((f0.repr x j / (s0 j : ℂ)) • f0 j) = _
      rw [map_smul, hfv, smul_smul, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr h)]
  have hKc : IsClosed (K : Set (Hilbert T)) := Submodule.isClosed_topologicalClosure _
  exact hKc.mem_of_tendsto (f0.hasSum_repr x)
    (Eventually.of_forall fun F => K.sum_mem fun j _ => hterm j)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- C4 from the three equality-case children. -/
theorem c4red [Countable I] [Countable J] (Phi : Channel I J) (rho sigma : State I)
    (hD : extendedRelativeEntropyNats rho.coefficients sigma.coefficients < ⊤)
    (heq : extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val sigma.coefficients) =
      extendedRelativeEntropyNats rho.coefficients sigma.coefficients) :
    petzRecovery Phi.val sigma.coefficients (Phi.val rho.coefficients) = rho.coefficients := by
  funext i j
  let rJ : State J := ⟨Phi.val rho.coefficients, chan_density Phi.val Phi.property _ rho.density⟩
  let sJ : State J := ⟨Phi.val sigma.coefficients, chan_density Phi.val Phi.property _ sigma.density⟩
  obtain ⟨ι, e, r, hr0, hr, hev⟩ := state_eigen rho
  obtain ⟨κ, f, s, hs0, hs, hfv⟩ := state_eigen sigma
  obtain ⟨ι0, e0, r0, hr0', hr', hev'⟩ := state_eigen rJ
  obtain ⟨κ0, f0, s0, hs0', hs', hfv'⟩ := state_eigen sJ
  have hRes := QAlgorithms.Papers.Independent.Gap48.P45.petz_equality_resolvent_and_supports Phi rho sigma e f r s hr0 hr.summable hev
    hs0 hs.summable hfv e0 f0 r0 s0 hr0' hr'.summable hev' hs0' hs'.summable hfv' hD heq
  have hKF := QAlgorithms.Papers.Independent.Gap48.P45.petz_equality_approximate_intertwiner Phi rho sigma e f r s hr0 hr.summable hev
    hs0 hs.summable hfv e0 f0 r0 s0 hr0' hr'.summable hev' hs0' hs'.summable hfv' hD hRes.1 hRes.2.1 hRes.2.2
  have hsupp' := hRes.2.2
  have ht := (sqrt_state sJ).1
  have hsq := (sqrt_state sigma).1
  have htf : ∀ k, positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) (f0 k) =
      ((Real.sqrt (s0 k) : ℝ) : ℂ) • f0 k := fun k =>
    psr_eig _ ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (bO_pos sJ)) (f0 k) (hs0' k) (hfv' k)
  have hsqf : ∀ k, positiveSquareRoot (boundedOperator sigma.coefficients) (f k) =
      ((Real.sqrt (s k) : ℝ) : ℂ) • f k := fun k =>
    psr_eig _ ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (bO_pos sigma)) (f k) (hs0 k) (hfv k)
  have hmain0 := QAlgorithms.Papers.Independent.Gap48.P45.petz_equality_matrix_entries Phi rho sigma e f r s hr0 hr hev hs0 hs.summable hfv
    e0 f0 r0 s0 hr0' hr' hev' hs0' hs'.summable hfv' hKF _ ht htf _ hsq hsqf (bvec j) (bvec i)
    (petzSupportedDual Phi.val sigma.coefficients (rk (bvec j) (bvec i)))
    (dual_rk Phi sigma (bvec j) (bvec i)).2
  have hmain : ∑' k, (r0 k : ℂ) * ⟪e0 k, petzSupportedDual Phi.val sigma.coefficients
      (rk (bvec j) (bvec i)) (e0 k)⟫_ℂ = ∑' k, (r k : ℂ) * ⟪e k, rk (bvec j) (bvec i) (e k)⟫_ℂ := hmain0
  unfold petzRecovery petzExtendedDual
  rw [unit_rk]
  set B := petzSupportedDual Phi.val sigma.coefficients (rk (bvec j) (bvec i)) with hBd
  set c := boundedTracePair sigma.coefficients (rk (bvec j) (bvec i)) with hcd
  set S := coefficientSupportProjection (Phi.val sigma.coefficients) with hSd
  have hterm : ∀ k, (r0 k : ℂ) * ⟪e0 k, (B + c • (ContinuousLinearMap.id ℂ (Hilbert J) - S)) (e0 k)⟫_ℂ =
      (r0 k : ℂ) * ⟪e0 k, B (e0 k)⟫_ℂ := by
    intro k
    rcases (hr0' k).lt_or_eq with hpos | hzero
    · have hS : S (e0 k) = e0 k := by
        rw [hSd]
        unfold coefficientSupportProjection
        exact Submodule.starProjection_eq_self_iff.mpr
          (supp_mem _ f0 s0 hfv' (e0 k) (fun l hl => hsupp' l k hl hpos))
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hS, sub_self, smul_zero,
        add_zero]
    · rw [← hzero]; simp
  refine (pair_eigen rJ e0 r0 hr0' hr'.summable hev' _).tsum_eq.symm.trans ?_
  rw [tsum_congr hterm, hmain, (pair_eigen rho e r hr0 hr.summable hev (rk (bvec j) (bvec i))).tsum_eq,
    bTP_rk, inner_bvec_left]
  have h3 := congrFun (congrFun (coeff_bO rho.density.1) i) j
  rw [← h3, operatorCoeff_apply]
  rfl

end P45C4J

end

end C4jPart

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

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity) in
theorem solution
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (rho sigma : State I)
    (hFinite : extendedRelativeEntropyNats rho.coefficients sigma.coefficients < ⊤) :
    IsTraceClassChannel (petzRecovery Phi.val sigma.coefficients) ∧
    ((extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val sigma.coefficients) =
        extendedRelativeEntropyNats rho.coefficients sigma.coefficients) ↔
      ReversibleOn Phi.val {rho, sigma}) ∧
    (ReversibleOn Phi.val {rho, sigma} ↔
      rho.coefficients = petzRecovery Phi.val sigma.coefficients (Phi.val rho.coefficients)) := by
  have hP := QAlgorithms.Papers.Independent.Gap48.P45.petzRecovery_isChannel_and_recovers_sigma Phi sigma
  have h3 : ∀ {I' J' : Type} [Countable I'] [Nonempty I'] (Psi : Matrix I' I' ℂ → Matrix J' J' ℂ),
      IsTraceClassChannel Psi → ∀ X Y : Matrix I' I' ℂ, IsDensity X → IsDensity Y →
      extendedRelativeEntropyNats (Psi X) (Psi Y) ≤ extendedRelativeEntropyNats X Y :=
    fun Psi hPsi X Y hX hY => QAlgorithms.Papers.Independent.Gap48.P45.extendedRelativeEntropy_monotone_of_finite_ssa
      (fun ρ σ hρ hρi hσ hσi => SimpleSSA.Monotone.eq_4 ρ σ hρ hρi hσ hσi) ⟨Psi, hPsi⟩ X Y hX hY
  have h4 : extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val sigma.coefficients) =
      extendedRelativeEntropyNats rho.coefficients sigma.coefficients →
      rho.coefficients = petzRecovery Phi.val sigma.coefficients (Phi.val rho.coefficients) :=
    fun h => (P45C4J.c4red Phi rho sigma hFinite h).symm
  have rev_of_rec : rho.coefficients =
      petzRecovery Phi.val sigma.coefficients (Phi.val rho.coefficients) →
      ReversibleOn Phi.val {rho, sigma} := by
    intro h
    refine ⟨_, hP.1, ?_⟩
    intro r hr
    rcases hr with rfl | hr
    · exact h.symm
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      exact hP.2
  have eq_of_rev : ReversibleOn Phi.val {rho, sigma} →
      extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val sigma.coefficients) =
        extendedRelativeEntropyNats rho.coefficients sigma.coefficients := by
    rintro ⟨R, hR, hfix⟩
    have a := h3 Phi.val Phi.property rho.coefficients sigma.coefficients rho.density
      sigma.density
    have b := h3 R hR (Phi.val rho.coefficients) (Phi.val sigma.coefficients)
      (P45Petz.chan_density Phi.val Phi.property _ rho.density)
      (P45Petz.chan_density Phi.val Phi.property _ sigma.density)
    rw [hfix rho (by simp), hfix sigma (by simp)] at b
    exact le_antisymm a b
  exact ⟨hP.1, ⟨fun h => rev_of_rec (h4 h), eq_of_rev⟩,
    ⟨fun h => h4 (eq_of_rev h), rev_of_rec⟩⟩

end

end ChildRoot

