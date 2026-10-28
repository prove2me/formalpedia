-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.petz_equality_matrix_entries
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T03:10:22.469082+00:00
-- url     : https://prove2.me/submissions/6f1d0d7e-b090-4e6b-91bb-595a3dbab6ea

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

lemma dual_add (Phi : Channel I J) (W1 W2 : Hilbert J →L[ℂ] Hilbert J) :
    channelDual Phi.val (W1 + W2) = channelDual Phi.val W1 + channelDual Phi.val W2 := by
  ext1 y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.add_apply, inner_add_right, channelDual_inner, channelDual_inner,
    channelDual_inner]
  have htc := Phi.property.1 _ (tc_rk y x)
  unfold dF dG boundedTracePair
  rw [← (pair_summable W1 htc).tsum_add (pair_summable W2 htc)]
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.add_comp, coeff_add]
  rfl

lemma dual_smul (Phi : Channel I J) (a : ℂ) (W : Hilbert J →L[ℂ] Hilbert J) :
    channelDual Phi.val (a • W) = a • channelDual Phi.val W := by
  ext1 y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, channelDual_inner, channelDual_inner]
  unfold dF dG boundedTracePair
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.smul_comp, coeff_smul]
  rfl

lemma sqn {x : ℝ} (hx : 0 ≤ x) (w : ℂ) : ‖(Real.sqrt x : ℂ) * w‖ ^ 2 = x * ‖w‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x), mul_pow,
    Real.sq_sqrt hx]

lemma sqn' {x : ℝ} (hx : 0 ≤ x) (w : ℂ) : ‖w * (Real.sqrt x : ℂ)‖ ^ 2 = ‖w‖ ^ 2 * x := by
  rw [mul_comm, sqn hx, mul_comm]

lemma coord_summable {T ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert T))
    (f : HilbertBasis κ ℂ (Hilbert T)) (s : κ → ℝ) (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (W : Hilbert T →L[ℂ] Hilbert T) :
    Summable fun p : κ × ι => s p.1 * ‖⟪f p.1, W (e p.2)⟫_ℂ‖ ^ 2 := by
  refine summable_prod_of_fibers_nonneg (fun p => mul_nonneg (hs0 _) (sq_nonneg _))
    (g := fun j => s j * ‖(ContinuousLinearMap.adjoint W) (f j)‖ ^ 2) (fun j => ?_) ?_
  · refine ((hb_norm_sq e ((ContinuousLinearMap.adjoint W) (f j))).mul_left (s j)).congr_fun
      fun i => ?_
    dsimp only
    rw [← ContinuousLinearMap.adjoint_inner_left W (e i) (f j), norm_inner_symm]
  · refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hs0 j) (sq_nonneg _)) (fun j => ?_)
      (hs1.mul_right (‖W‖ ^ 2))
    have hle : ‖(ContinuousLinearMap.adjoint W) (f j)‖ ≤ ‖W‖ := by
      calc _ ≤ ‖ContinuousLinearMap.adjoint W‖ * ‖f j‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖W‖ := by rw [LinearIsometryEquiv.norm_map, f.orthonormal.1 j, mul_one]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hle 2) (hs0 j)

lemma rsum {T ι κ : Type} (e : HilbertBasis ι ℂ (Hilbert T)) (f : HilbertBasis κ ℂ (Hilbert T))
    {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (hrs : Summable r) :
    Summable fun p : κ × ι => ‖⟪f p.1, e p.2⟫_ℂ * (Real.sqrt (r p.2) : ℂ)‖ ^ 2 := by
  refine summable_prod_of_fibers_nonneg' (fun p => sq_nonneg _) (g := r) (fun i => ?_) hrs
  have h := (hb_norm_sq f (e i)).mul_right (r i)
  rw [e.orthonormal.1 i, one_pow, one_mul] at h
  refine h.congr_fun fun j => ?_
  dsimp only
  rw [sqn' (hr i)]

lemma memℓ2 {T : Type} (g : T → ℂ) (hg : Summable fun m => ‖g m‖ ^ 2) : Memℓp g 2 := by
  refine memℓp_gen (hg.congr fun m => ?_)
  rw [ENNReal.toReal_ofNat, Real.rpow_two]

lemma l2_sq {T : Type} (v : lp (fun _ : T => ℂ) 2) : HasSum (fun m => ‖v m‖ ^ 2) (‖v‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) v
  rw [ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

section Pair

variable (Phi : Channel I J) {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I))
  (f : HilbertBasis κ ℂ (Hilbert I)) (s : κ → ℝ) (e0 : HilbertBasis ι0 ℂ (Hilbert J))
  (f0 : HilbertBasis κ0 ℂ (Hilbert J)) (s0 : κ0 → ℝ)

/-- Coordinates of the operator pair (sigma0^{1/2} Z, sigma^{1/2} Phi*(Z)). -/
def opc (Z : Hilbert J →L[ℂ] Hilbert J) : (κ0 × ι0) ⊕ (κ × ι) → ℂ :=
  Sum.elim (fun p => (Real.sqrt (s0 p.1) : ℂ) * ⟪f0 p.1, Z (e0 p.2)⟫_ℂ)
    (fun p => (Real.sqrt (s p.1) : ℂ) * ⟪f p.1, channelDual Phi.val Z (e p.2)⟫_ℂ)

/-- Coordinates of the pair (rho0^{1/2}, rho^{1/2}). -/
def Rc (r : ι → ℝ) (r0 : ι0 → ℝ) : (κ0 × ι0) ⊕ (κ × ι) → ℂ :=
  Sum.elim (fun p => ⟪f0 p.1, e0 p.2⟫_ℂ * (Real.sqrt (r0 p.2) : ℂ))
    (fun p => ⟪f p.1, e p.2⟫_ℂ * (Real.sqrt (r p.2) : ℂ))

lemma opc_mem (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s) (hs0' : ∀ j, 0 ≤ s0 j)
    (hs1' : Summable s0) (Z : Hilbert J →L[ℂ] Hilbert J) :
    Memℓp (opc Phi e f s e0 f0 s0 Z) 2 := by
  refine memℓ2 _ (Summable.sum _ ?_ ?_)
  · refine (coord_summable e0 f0 s0 hs0' hs1' Z).congr fun p => ?_
    simp only [Function.comp_apply, opc, Sum.elim_inl]
    rw [sqn (hs0' _)]
  · refine (coord_summable e f s hs0 hs1 (channelDual Phi.val Z)).congr fun p => ?_
    simp only [Function.comp_apply, opc, Sum.elim_inr]
    rw [sqn (hs0 _)]

lemma Rc_sq (r : ι → ℝ) (r0 : ι0 → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr1' : Summable r0) :
    Summable fun m => ‖Rc e f e0 f0 r r0 m‖ ^ 2 :=
  Summable.sum _ (rsum e0 f0 hr0' hr1') (rsum e f hr0 hr1)

/-- The operator-pair map Z ↦ (sigma0^{1/2} Z, sigma^{1/2} Phi*(Z)) into ℓ². -/
def opPair (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s) (hs0' : ∀ j, 0 ≤ s0 j)
    (hs1' : Summable s0) :
    (Hilbert J →L[ℂ] Hilbert J) →ₗ[ℂ] lp (fun _ : (κ0 × ι0) ⊕ (κ × ι) => ℂ) 2 where
  toFun Z := ⟨opc Phi e f s e0 f0 s0 Z, opc_mem Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z⟩
  map_add' Z1 Z2 := by
    ext m
    rcases m with p | p
    · show opc Phi e f s e0 f0 s0 (Z1 + Z2) (Sum.inl p) =
        opc Phi e f s e0 f0 s0 Z1 (Sum.inl p) + opc Phi e f s e0 f0 s0 Z2 (Sum.inl p)
      simp only [opc, Sum.elim_inl, ContinuousLinearMap.add_apply, inner_add_right, mul_add]
    · show opc Phi e f s e0 f0 s0 (Z1 + Z2) (Sum.inr p) =
        opc Phi e f s e0 f0 s0 Z1 (Sum.inr p) + opc Phi e f s e0 f0 s0 Z2 (Sum.inr p)
      simp only [opc, Sum.elim_inr, dual_add, ContinuousLinearMap.add_apply, inner_add_right,
        mul_add]
  map_smul' a Z := by
    ext m
    rcases m with p | p
    · show opc Phi e f s e0 f0 s0 (a • Z) (Sum.inl p) = a * opc Phi e f s e0 f0 s0 Z (Sum.inl p)
      simp only [opc, Sum.elim_inl, ContinuousLinearMap.smul_apply, inner_smul_right]
      ring
    · show opc Phi e f s e0 f0 s0 (a • Z) (Sum.inr p) = a * opc Phi e f s e0 f0 s0 Z (Sum.inr p)
      simp only [opc, Sum.elim_inr, dual_smul, ContinuousLinearMap.smul_apply, inner_smul_right]
      ring

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

/-- K-g (LA side): Parseval for the rank-one input observable. -/
lemma la_hasSum {T ι : Type} (e : HilbertBasis ι ℂ (Hilbert T)) (s W : Hilbert T →L[ℂ] Hilbert T)
    (hs : ContinuousLinearMap.adjoint s = s) (u v : Hilbert T) :
    HasSum (fun i => ⟪s (W (e i)), rk u v (s (W (e i)))⟫_ℂ)
      ⟪s v, W (ContinuousLinearMap.adjoint W (s u))⟫_ℂ := by
  have h := e.hasSum_inner_mul_inner (ContinuousLinearMap.adjoint W (s v))
    (ContinuousLinearMap.adjoint W (s u))
  rw [ContinuousLinearMap.adjoint_inner_left] at h
  refine h.congr_fun fun i => ?_
  rw [rk_apply, inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, sa_swap hs, sa_swap hs (W (e i)) u]

/-- The Kadison-Schwarz defect D = Phi*(Z Z*) - Phi*(Z) Phi*(Z)* is positive. -/
lemma defect_pos (Phi : Channel I J) (Z : Hilbert J →L[ℂ] Hilbert J) :
    0 ≤ channelDual Phi.val (Z.comp (ContinuousLinearMap.adjoint Z)) -
      (channelDual Phi.val Z).comp (ContinuousLinearMap.adjoint (channelDual Phi.val Z)) := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  set W := channelDual Phi.val Z
  have hsa : IsSelfAdjoint (channelDual Phi.val (Z.comp (ContinuousLinearMap.adjoint Z)) -
      W.comp (ContinuousLinearMap.adjoint W)) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    rw [map_sub, dual_adj, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  refine ⟨hsa.isSymmetric, fun x => ?_⟩
  have hks := ks_vec Phi (ContinuousLinearMap.adjoint Z) x
  rw [ContinuousLinearMap.adjoint_adjoint, ← dual_adj] at hks
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.sub_apply, inner_sub_left,
    map_sub, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_right W ((ContinuousLinearMap.adjoint W) x) x,
    inner_self_eq_norm_sq]
  have h4 : RCLike.re ⟪channelDual Phi.val (Z.comp (ContinuousLinearMap.adjoint Z)) x, x⟫_ℂ =
      (⟪x, channelDual Phi.val (Z.comp (ContinuousLinearMap.adjoint Z)) x⟫_ℂ).re := by
    rw [← inner_conj_symm]; exact Complex.conj_re _
  rw [h4]
  linarith

/-- |<s v, D s u>| <= |u| |v| Sum_k q_k Re<f_k, D f_k> for D >= 0 and s f_k = sqrt(q_k) f_k. -/
lemma defect_bound {E κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D s : E →L[ℂ] E) (hD : 0 ≤ D) (hs : ContinuousLinearMap.adjoint s = s)
    (f : HilbertBasis κ ℂ E) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hsf : ∀ k, s (f k) = ((Real.sqrt (q k) : ℝ) : ℂ) • f k)
    {S : ℝ} (hS : HasSum (fun k => q k * (⟪f k, D (f k)⟫_ℂ).re) S) (u v : E) :
    ‖⟪s v, D (s u)⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ * S := by
  obtain ⟨hRa, hRR⟩ := psr_facts D hD
  set R := QAlgorithms.Papers.Independent.Next46.P31.positiveSquareRoot D with hRdef
  set T := R.comp s with hT
  have hTf : HasSum (fun k => ‖T (f k)‖ ^ 2) S := by
    refine hS.congr_fun fun k => ?_
    rw [hT, ContinuousLinearMap.comp_apply, hsf, map_smul, norm_smul, mul_pow,
      sa_norm_sq hRa hRR (f k), Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hq k)]
  have hS0 : 0 ≤ S := hasSum_le (fun k => sq_nonneg _) hasSum_zero hTf
  have hTa := hs_swap f f T hTf
  have hnorm : ∀ x : E, ‖T x‖ ≤ Real.sqrt S * ‖x‖ := by
    intro x
    have h1 := hb_norm_sq f (T x)
    have h2 : ‖T x‖ ^ 2 ≤ S * ‖x‖ ^ 2 := by
      refine hasSum_le (fun m => ?_) h1 (hTa.mul_right (‖x‖ ^ 2))
      rw [← ContinuousLinearMap.adjoint_inner_left, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    have h3 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hS0, Real.sqrt_sq (norm_nonneg _)] at h3
  have heq : ⟪s v, D (s u)⟫_ℂ = ⟪T v, T u⟫_ℂ := by
    rw [hT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hRR,
      ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left, hRa]
  rw [heq]
  calc ‖⟪T v, T u⟫_ℂ‖ ≤ ‖T v‖ * ‖T u‖ := norm_inner_le_norm _ _
    _ ≤ (Real.sqrt S * ‖v‖) * (Real.sqrt S * ‖u‖) :=
        mul_le_mul (hnorm v) (hnorm u) (norm_nonneg _) (by positivity)
    _ = ‖u‖ * ‖v‖ * (Real.sqrt S * Real.sqrt S) := by ring
    _ = ‖u‖ * ‖v‖ * S := by rw [Real.mul_self_sqrt hS0]

lemma lb_term (Phi : Channel I J) (a b : Hilbert I) (t B : Hilbert J →L[ℂ] Hilbert J)
    (ht : ContinuousLinearMap.adjoint t = t)
    (hB : t.comp (B.comp t) = boundedOperator (Phi.val (operatorCoeff (rk a b)))) (p : Hilbert J) :
    ⟪t p, B (t p)⟫_ℂ = ⟪b, channelDual Phi.val (rk p p) a⟫_ℂ := by
  have h1 : ⟪t p, B (t p)⟫_ℂ = ⟪p, boundedOperator (Phi.val (operatorCoeff (rk a b))) p⟫_ℂ := by
    rw [← hB, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, sa_swap ht]
  rw [h1, ← bTP_rk]
  change dF Phi (rk p p) b a = _
  rw [← channelDual_inner]

lemma swap_sum {T K ι0 : Type}
    (e0 : HilbertBasis ι0 ℂ (Hilbert T)) (Z Y : Hilbert T →L[ℂ] Hilbert T) (hY : ∀ x y, ⟪Y x, y⟫_ℂ = ⟪x, Z y⟫_ℂ) (w0 w1 : K → Hilbert T)
    (hw0 : Summable fun k => ‖w0 k‖ ^ 2) (hw1 : Summable fun k => ‖w1 k‖ ^ 2) :
    HasSum (fun i => ∑' k, ⟪w1 k, Z (e0 i)⟫_ℂ * ⟪Z (e0 i), w0 k⟫_ℂ)
      (∑' k, ⟪Y (w1 k), Y (w0 k)⟫_ℂ) := by
  have hY' : ∀ x y, ⟪x, Y y⟫_ℂ = ⟪Z x, y⟫_ℂ := by
    intro x y; rw [← inner_conj_symm, hY, inner_conj_symm]
  have hg : Summable (fun p : K × ι0 =>
      (‖⟪e0 p.2, Y (w1 p.1)⟫_ℂ‖ ^ 2 +
        ‖⟪e0 p.2, Y (w0 p.1)⟫_ℂ‖ ^ 2) / 2) := by
    refine summable_prod_of_fibers_nonneg
      (fun p => div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_two)
      (g := fun k => (‖Y (w1 k)‖ ^ 2 +
        ‖Y (w0 k)‖ ^ 2) / 2) (fun k => ?_) ?_
    · exact ((hb_norm_sq e0 (Y (w1 k))).add (hb_norm_sq e0 (Y (w0 k)))).div_const 2
    · refine Summable.of_nonneg_of_le
        (fun k => div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_two) (fun k => ?_)
        (((hw1.add hw0).mul_left (‖Y‖ ^ 2)).div_const 2)
      have h1 : ‖Y (w1 k)‖ ^ 2 ≤
          ‖Y‖ ^ 2 * ‖w1 k‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (Y.le_opNorm _) 2
      have h0 : ‖Y (w0 k)‖ ^ 2 ≤
          ‖Y‖ ^ 2 * ‖w0 k‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (Y.le_opNorm _) 2
      show (‖Y (w1 k)‖ ^ 2 + ‖Y (w0 k)‖ ^ 2) / 2
        ≤ ‖Y‖ ^ 2 * (‖w1 k‖ ^ 2 + ‖w0 k‖ ^ 2) / 2
      nlinarith
  have hF : Summable (fun p : ι0 × K => ⟪w1 p.2, Z (e0 p.1)⟫_ℂ * ⟪Z (e0 p.1), w0 p.2⟫_ℂ) := by
    have hg' := (Equiv.summable_iff (Equiv.prodComm ι0 K)).mpr hg
    refine Summable.of_norm_bounded hg' (fun p => ?_)
    show ‖⟪w1 p.2, Z (e0 p.1)⟫_ℂ * ⟪Z (e0 p.1), w0 p.2⟫_ℂ‖ ≤
      (‖⟪e0 p.1, Y (w1 p.2)⟫_ℂ‖ ^ 2 +
        ‖⟪e0 p.1, Y (w0 p.2)⟫_ℂ‖ ^ 2) / 2
    rw [norm_mul, hY', hY',
      norm_inner_symm (w1 p.2)]
    nlinarith [sq_nonneg (‖⟪Z (e0 p.1), w1 p.2⟫_ℂ‖ - ‖⟪Z (e0 p.1), w0 p.2⟫_ℂ‖)]
  have hsum := hF.hasSum.prod_fiberwise (fun i => (hF.prod_factor i).hasSum)
  have hF2 := (Equiv.summable_iff (Equiv.prodComm K ι0)).mpr hF
  have hsum2 := hF2.hasSum.prod_fiberwise (fun k => (hF2.prod_factor k).hasSum)
  have heqv := Equiv.tsum_eq (Equiv.prodComm K ι0)
    (fun p : ι0 × K => ⟪w1 p.2, Z (e0 p.1)⟫_ℂ * ⟪Z (e0 p.1), w0 p.2⟫_ℂ)
  have hfib : ∀ k, HasSum (fun i => ⟪w1 k, Z (e0 i)⟫_ℂ * ⟪Z (e0 i), w0 k⟫_ℂ)
      ⟪Y (w1 k), Y (w0 k)⟫_ℂ := by
    intro k
    refine (e0.hasSum_inner_mul_inner _ _).congr_fun fun i => ?_
    rw [hY, hY']
  have hsum2' : HasSum (fun k => ⟪Y (w1 k),
      Y (w0 k)⟫_ℂ)
      (∑' p : ι0 × K, ⟪w1 p.2, Z (e0 p.1)⟫_ℂ * ⟪Z (e0 p.1), w0 p.2⟫_ℂ) := by
    rw [← heqv]
    exact hsum2.congr_fun fun k => ((hfib k).tsum_eq).symm
  rw [hsum2'.tsum_eq]
  exact hsum

/-- K-g (LB side): Sum_i <t Z e0_i, B t Z e0_i> = <b, Phi*(Z Z*) a> when t B t = Phi(|a><b|). -/
lemma lb_hasSum (Phi : Channel I J) (a b : Hilbert I) {ι0 : Type}
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (t B Z : Hilbert J →L[ℂ] Hilbert J)
    (ht : ContinuousLinearMap.adjoint t = t)
    (hB : t.comp (B.comp t) = boundedOperator (Phi.val (operatorCoeff (rk a b)))) :
    HasSum (fun i => ⟪t (Z (e0 i)), B (t (Z (e0 i)))⟫_ℂ)
      ⟪b, channelDual Phi.val (Z.comp (ContinuousLinearMap.adjoint Z)) a⟫_ℂ := by
  obtain ⟨K, w, hw, hw2⟩ := blk2 Phi ![a, b]
  have hterm : ∀ i, ⟪t (Z (e0 i)), B (t (Z (e0 i)))⟫_ℂ =
      ∑' k, ⟪w 1 k, Z (e0 i)⟫_ℂ * ⟪Z (e0 i), w 0 k⟫_ℂ := by
    intro i
    rw [lb_term Phi a b t B ht hB]
    have h2 := (hw2 0 1 (rk (Z (e0 i)) (Z (e0 i)))).tsum_eq
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    rw [← h2]
    refine tsum_congr fun k => ?_
    rw [rk_apply, inner_smul_right, mul_comm]
  have hout := hw2 0 1 (Z.comp (ContinuousLinearMap.adjoint Z))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hout
  have hval : ∑' k, ⟪ContinuousLinearMap.adjoint Z (w 1 k), ContinuousLinearMap.adjoint Z (w 0 k)⟫_ℂ =
      ⟪b, channelDual Phi.val (Z.comp (ContinuousLinearMap.adjoint Z)) a⟫_ℂ := by
    rw [← hout.tsum_eq]
    refine tsum_congr fun k => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  rw [← hval]
  exact (swap_sum e0 Z (ContinuousLinearMap.adjoint Z)
    (fun x y => ContinuousLinearMap.adjoint_inner_left Z y x) (w 0) (w 1) (hw 0) (hw 1)).congr_fun hterm

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

lemma lpE_sq {ι : Type} (y : lp (fun _ : ι => E) 2) : HasSum (fun i => ‖y i‖ ^ 2) (‖y‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) y
  rw [ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

lemma memE {ι : Type} (g : ι → E) (hg : Summable fun m => ‖g m‖ ^ 2) : Memℓp g 2 := by
  refine memℓp_gen (hg.congr fun m => ?_)
  rw [ENNReal.toReal_ofNat, Real.rpow_two]

variable {T κ ι : Type} (f : HilbertBasis κ ℂ E) (π : ι × κ → T) (hπ : Function.Injective π)

include hπ

lemma pi_sum (v : lp (fun _ : T => ℂ) 2) : Summable fun p : ι × κ => ‖v (π p)‖ ^ 2 :=
  (l2_sq v).summable.comp_injective hπ

/-- The i-th slice of v along π. -/
def slc (v : lp (fun _ : T => ℂ) 2) (i : ι) : lp (fun _ : κ => ℂ) 2 :=
  ⟨fun j => v (π (i, j)), memℓ2 _ ((pi_sum π hπ v).prod_factor i)⟩

/-- The vector with f-coordinates the i-th slice of v. -/
def xc (v : lp (fun _ : T => ℂ) 2) (i : ι) : E := f.repr.symm (slc π hπ v i)

lemma xc_sq (v : lp (fun _ : T => ℂ) 2) (i : ι) :
    HasSum (fun j => ‖v (π (i, j))‖ ^ 2) (‖xc f π hπ v i‖ ^ 2) := by
  rw [xc, LinearIsometryEquiv.norm_map]
  exact l2_sq (slc π hπ v i)

lemma xc_tot (v : lp (fun _ : T => ℂ) 2) :
    HasSum (fun i => ‖xc f π hπ v i‖ ^ 2) (∑' p, ‖v (π p)‖ ^ 2) :=
  (pi_sum π hπ v).hasSum.prod_fiberwise (fun i => xc_sq f π hπ v i)

lemma xc_le (v : lp (fun _ : T => ℂ) 2) : ∑' p, ‖v (π p)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [← (l2_sq v).tsum_eq]
  exact tsum_comp_le_tsum_of_inj (l2_sq v).summable (fun _ => sq_nonneg _) hπ

lemma xc_eq (v : lp (fun _ : T => ℂ) 2) (i : ι) (y : E) (hy : ∀ j, v (π (i, j)) = ⟪f j, y⟫_ℂ) :
    xc f π hπ v i = y := by
  rw [xc, LinearIsometryEquiv.symm_apply_eq]
  ext j
  rw [HilbertBasis.repr_apply_apply]
  exact hy j

def Xl : lp (fun _ : T => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => E) 2 where
  toFun v := ⟨xc f π hπ v, memE _ (xc_tot f π hπ v).summable⟩
  map_add' v w := by
    ext i
    show xc f π hπ (v + w) i = xc f π hπ v i + xc f π hπ w i
    have : slc π hπ (v + w) i = slc π hπ v i + slc π hπ w i := by ext j; rfl
    simp only [xc, this, map_add]
  map_smul' a v := by
    ext i
    show xc f π hπ (a • v) i = a • xc f π hπ v i
    have : slc π hπ (a • v) i = a • slc π hπ v i := by ext j; rfl
    simp only [xc, this, map_smul]

lemma Xl_norm (v : lp (fun _ : T => ℂ) 2) : ‖Xl f π hπ v‖ ≤ 1 * ‖v‖ := by
  rw [one_mul]
  have h1 : ‖Xl f π hπ v‖ ^ 2 = ∑' p, ‖v (π p)‖ ^ 2 :=
    (lpE_sq (Xl f π hπ v)).unique (xc_tot f π hπ v)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (h1 ▸ xc_le π hπ v)

/-- The coordinate map as a continuous linear map. -/
def Xm : lp (fun _ : T => ℂ) 2 →L[ℂ] lp (fun _ : ι => E) 2 :=
  (Xl f π hπ).mkContinuous 1 (Xl_norm f π hπ)

lemma Xm_apply (v : lp (fun _ : T => ℂ) 2) (i : ι) : Xm f π hπ v i = xc f π hπ v i := rfl

lemma Xm_sq (v : lp (fun _ : T => ℂ) 2) :
    HasSum (fun i => ‖xc f π hπ v i‖ ^ 2) (‖Xm f π hπ v‖ ^ 2) :=
  lpE_sq (Xm f π hπ v)

end Gen

section Pw

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type}

lemma pw_sum (M : E →L[ℂ] E) (y : lp (fun _ : ι => E) 2) :
    Summable fun i => ‖M (y i)‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => by rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (M.le_opNorm _) 2)
    ((lpE_sq y).summable.mul_left (‖M‖ ^ 2))

def Pl (M : E →L[ℂ] E) : lp (fun _ : ι => E) 2 →ₗ[ℂ] lp (fun _ : ι => E) 2 where
  toFun y := ⟨fun i => M (y i), memE _ (pw_sum M y)⟩
  map_add' y z := by
    ext i
    show M ((y + z) i) = M (y i) + M (z i)
    rw [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' a y := by
    ext i
    show M ((a • y) i) = a • M (y i)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul]

lemma Pl_norm (M : E →L[ℂ] E) (y : lp (fun _ : ι => E) 2) : ‖Pl M y‖ ≤ ‖M‖ * ‖y‖ := by
  have h1 : HasSum (fun i => ‖M (y i)‖ ^ 2) (‖Pl M y‖ ^ 2) := lpE_sq (Pl M y)
  have h2 : ‖Pl M y‖ ^ 2 ≤ (‖M‖ * ‖y‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun i => ?_) h1 ((lpE_sq y).mul_left (‖M‖ ^ 2))
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (M.le_opNorm _) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

def Pm (M : E →L[ℂ] E) : lp (fun _ : ι => E) 2 →L[ℂ] lp (fun _ : ι => E) 2 :=
  (Pl M).mkContinuous ‖M‖ (Pl_norm M)

lemma Pm_quad (M : E →L[ℂ] E) (y : lp (fun _ : ι => E) 2) :
    HasSum (fun i => ⟪y i, M (y i)⟫_ℂ) ⟪y, Pm M y⟫_ℂ :=
  lp.hasSum_inner y (Pm M y)

end Pw

/-! ### Trace identities -/

lemma n_hasSum {T ι κ : Type} (rho : State T) (e : HilbertBasis ι ℂ (Hilbert T))
    (f : HilbertBasis κ ℂ (Hilbert T)) (q : κ → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : Summable q)
    (hfv : ∀ j, boundedOperator rho.coefficients (f j) = (q j : ℂ) • f j)
    (t : Hilbert T →L[ℂ] Hilbert T) (ht : ContinuousLinearMap.adjoint t = t)
    (htf : ∀ j, t (f j) = ((Real.sqrt (q j) : ℝ) : ℂ) • f j) (Z : Hilbert T →L[ℂ] Hilbert T) :
    HasSum (fun i => ‖t (Z (e i))‖ ^ 2)
      (boundedTracePair rho.coefficients (Z.comp (ContinuousLinearMap.adjoint Z))).re := by
  have h1 := pair_eigen_sq rho f q hq0 hq1 hfv (ContinuousLinearMap.adjoint Z)
  rw [ContinuousLinearMap.adjoint_adjoint] at h1
  have h2 : HasSum (fun j => ‖ContinuousLinearMap.adjoint (t.comp Z) (f j)‖ ^ 2)
      (boundedTracePair rho.coefficients (Z.comp (ContinuousLinearMap.adjoint Z))).re := by
    refine h1.congr_fun fun j => ?_
    rw [ContinuousLinearMap.adjoint_comp, ht, ContinuousLinearMap.comp_apply, htf, map_smul,
      norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hq0 j)]
  have h3 := hs_swap e f (ContinuousLinearMap.adjoint (t.comp Z)) h2
  rw [ContinuousLinearMap.adjoint_adjoint] at h3
  exact h3

lemma q_hasSum {T κ : Type} (rho : State T) (f : HilbertBasis κ ℂ (Hilbert T)) (q : κ → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : Summable q)
    (hfv : ∀ j, boundedOperator rho.coefficients (f j) = (q j : ℂ) • f j)
    (A : Hilbert T →L[ℂ] Hilbert T) :
    HasSum (fun k => q k * (⟪f k, A (f k)⟫_ℂ).re) (boundedTracePair rho.coefficients A).re :=
  (Complex.hasSum_re (pair_eigen rho f q hq0 hq1 hfv A)).congr_fun fun k => by
    rw [Complex.re_ofReal_mul]

lemma D_hasSum (Phi : Channel I J) (sigma : State I) {κ : Type}
    (f : HilbertBasis κ ℂ (Hilbert I)) (q : κ → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : Summable q)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (q j : ℂ) • f j)
    (Z : Hilbert J →L[ℂ] Hilbert J) :
    HasSum (fun k => q k * (⟪f k, (channelDual Phi.val (Z.comp (ContinuousLinearMap.adjoint Z)) -
        (channelDual Phi.val Z).comp (ContinuousLinearMap.adjoint (channelDual Phi.val Z))) (f k)⟫_ℂ).re)
      ((boundedTracePair (Phi.val sigma.coefficients) (Z.comp (ContinuousLinearMap.adjoint Z))).re -
        (boundedTracePair sigma.coefficients ((channelDual Phi.val Z).comp
          (ContinuousLinearMap.adjoint (channelDual Phi.val Z)))).re) := by
  set W := channelDual Phi.val Z
  have h1 := q_hasSum sigma f q hq0 hq1 hfv (channelDual Phi.val (Z.comp (ContinuousLinearMap.adjoint Z)))
  rw [dual_pair Phi _ _ sigma.density.1] at h1
  have h2 := pair_eigen_sq sigma f q hq0 hq1 hfv (ContinuousLinearMap.adjoint W)
  rw [ContinuousLinearMap.adjoint_adjoint] at h2
  refine (h1.sub h2).congr_fun fun k => ?_
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re, mul_sub,
    ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left W ((ContinuousLinearMap.adjoint W) (f k)) (f k),
    inner_self_eq_norm_sq_to_K]
  congr 2
  norm_cast

/-! ### MAIN (K-g) -/

def pi0 (κ0 ι0 κ ι : Type) : ι0 × κ0 → (κ0 × ι0) ⊕ (κ × ι) := fun p => Sum.inl (p.2, p.1)
def pi1 (κ0 ι0 κ ι : Type) : ι × κ → (κ0 × ι0) ⊕ (κ × ι) := fun p => Sum.inr (p.2, p.1)

lemma pi0_inj (κ0 ι0 κ ι : Type) : Function.Injective (pi0 κ0 ι0 κ ι) := fun a b h => by
  simp only [pi0, Sum.inl.injEq, Prod.mk.injEq] at h; exact Prod.ext h.2 h.1

lemma pi1_inj (κ0 ι0 κ ι : Type) : Function.Injective (pi1 κ0 ι0 κ ι) := fun a b h => by
  simp only [pi1, Sum.inr.injEq, Prod.mk.injEq] at h; exact Prod.ext h.2 h.1

lemma smul_sq_norm {T ι : Type} (e : HilbertBasis ι ℂ (Hilbert T)) {x : ℝ} (hx : 0 ≤ x) (i : ι) :
    ‖((Real.sqrt x : ℝ) : ℂ) • e i‖ ^ 2 = x := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, e.orthonormal.1 i, mul_one, sq_abs,
    Real.sq_sqrt hx]

lemma smul_quad {T ι : Type} (e : HilbertBasis ι ℂ (Hilbert T)) (M : Hilbert T →L[ℂ] Hilbert T)
    {x : ℝ} (hx : 0 ≤ x) (i : ι) :
    ⟪((Real.sqrt x : ℝ) : ℂ) • e i, M (((Real.sqrt x : ℝ) : ℂ) • e i)⟫_ℂ =
      (x : ℂ) * ⟪e i, M (e i)⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

/-- MAIN bridge: the epsilon-approximation form of K-f gives membership of the target pair
(rho0^{1/2}, rho^{1/2}) in the closure of the range of the operator-pair map. -/
lemma approx_mem (Phi : Channel I J) {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I))
    (f : HilbertBasis κ ℂ (Hilbert I)) (r : ι → ℝ) (s : κ → ℝ)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r) (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr1' : Summable r0) (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ Z : Hilbert J →L[ℂ] Hilbert J,
      (∑' p : κ0 × ι0, ‖(Real.sqrt (s0 p.1) : ℂ) * ⟪f0 p.1, Z (e0 p.2)⟫_ℂ -
          ⟪f0 p.1, e0 p.2⟫_ℂ * (Real.sqrt (r0 p.2) : ℂ)‖ ^ 2) +
      (∑' p : κ × ι, ‖(Real.sqrt (s p.1) : ℂ) * ⟪f p.1, channelDual Phi.val Z (e p.2)⟫_ℂ -
          ⟪f p.1, e p.2⟫_ℂ * (Real.sqrt (r p.2) : ℂ)‖ ^ 2) < ε) :
    (⟨Rc e f e0 f0 r r0, memℓ2 _ (Rc_sq e f e0 f0 r r0 hr0 hr1 hr0' hr1')⟩ :
        lp (fun _ : (κ0 × ι0) ⊕ (κ × ι) => ℂ) 2) ∈
      (LinearMap.range (opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1')).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range,
    Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨Z, hZ⟩ := happ (ε ^ 2) (by positivity)
  refine ⟨opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z, ⟨Z, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  set R : lp (fun _ : (κ0 × ι0) ⊕ (κ × ι) => ℂ) 2 :=
    ⟨Rc e f e0 f0 r r0, memℓ2 _ (Rc_sq e f e0 f0 r r0 hr0 hr1 hr0' hr1')⟩ with hR
  set W := opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z with hW
  set g : (κ0 × ι0) ⊕ (κ × ι) → ℝ :=
    fun m => ‖opc Phi e f s e0 f0 s0 Z m - Rc e f e0 f0 r r0 m‖ ^ 2 with hg
  have hN : HasSum (fun m => ‖(R - W) m‖ ^ 2) (‖R - W‖ ^ 2) := by
    have := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (R - W)
    simpa using this
  have hN' : HasSum g (‖R - W‖ ^ 2) := hN.congr_fun fun m => by
    rw [lp.coeFn_sub, Pi.sub_apply, norm_sub_rev]
    rfl
  have hA : HasSum (g ∘ Sum.inl) (∑' p, (g ∘ Sum.inl) p) :=
    (hN'.summable.comp_injective Sum.inl_injective).hasSum
  have hB : HasSum (g ∘ Sum.inr) (∑' p, (g ∘ Sum.inr) p) :=
    (hN'.summable.comp_injective Sum.inr_injective).hasSum
  have hlt : ‖R - W‖ ^ 2 < ε ^ 2 := by
    rw [hN'.unique (HasSum.sum (f := g) hA hB)]
    exact hZ
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

section Main

variable [Countable I] [Countable J]

theorem main_eq (Phi : Channel I J) (rho sigma : State I)
    {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr : HasSum r 1)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr' : HasSum r0 1)
    (hev' : ∀ i, boundedOperator (Phi.val rho.coefficients) (e0 i) = (r0 i : ℂ) • e0 i)
    (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (hfv' : ∀ j, boundedOperator (Phi.val sigma.coefficients) (f0 j) = (s0 j : ℂ) • f0 j)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ Z : Hilbert J →L[ℂ] Hilbert J,
      (∑' p : κ0 × ι0, ‖(Real.sqrt (s0 p.1) : ℂ) * ⟪f0 p.1, Z (e0 p.2)⟫_ℂ -
          ⟪f0 p.1, e0 p.2⟫_ℂ * (Real.sqrt (r0 p.2) : ℂ)‖ ^ 2) +
      (∑' p : κ × ι, ‖(Real.sqrt (s p.1) : ℂ) * ⟪f p.1, channelDual Phi.val Z (e p.2)⟫_ℂ -
          ⟪f p.1, e p.2⟫_ℂ * (Real.sqrt (r p.2) : ℂ)‖ ^ 2) < ε)
    (t : Hilbert J →L[ℂ] Hilbert J) (ht : ContinuousLinearMap.adjoint t = t)
    (htf : ∀ j, t (f0 j) = ((Real.sqrt (s0 j) : ℝ) : ℂ) • f0 j)
    (sq : Hilbert I →L[ℂ] Hilbert I) (hsq : ContinuousLinearMap.adjoint sq = sq)
    (hsqf : ∀ j, sq (f j) = ((Real.sqrt (s j) : ℝ) : ℂ) • f j)
    (u v : Hilbert I) (B : Hilbert J →L[ℂ] Hilbert J)
    (hB : t.comp (B.comp t) = boundedOperator (Phi.val (operatorCoeff (rk (sq u) (sq v))))) :
    ∑' i, (r0 i : ℂ) * ⟪e0 i, B (e0 i)⟫_ℂ = ∑' i, (r i : ℂ) * ⟪e i, rk u v (e i)⟫_ℂ := by
  let sJ : State J := ⟨Phi.val sigma.coefficients, chan_density Phi.val Phi.property _ sigma.density⟩
  have hsub : closure (Set.range (opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1')) ⊆
      {w | ‖⟪Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) w,
            Pm B (Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) w)⟫_ℂ -
          ⟪Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) w,
            Pm (rk u v) (Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) w)⟫_ℂ‖ ≤
        ‖u‖ * ‖v‖ * (‖Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) w‖ ^ 2 -
          ‖Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) w‖ ^ 2)} := by
    refine closure_minimal ?_ (isClosed_le ?_ ?_)
    · rintro _ ⟨Z, rfl⟩
      simp only [Set.mem_setOf_eq]
      have hx0 : ∀ i, Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι)
          (opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z) i = t (Z (e0 i)) := fun i => by
        rw [Xm_apply]
        refine xc_eq f0 _ _ _ i _ fun j => ?_
        show opc Phi e f s e0 f0 s0 Z (Sum.inl (j, i)) = _
        simp only [opc, Sum.elim_inl]
        rw [sa_swap ht, htf, inner_smul_left, Complex.conj_ofReal]
      have hx1 : ∀ i, Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι)
          (opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z) i =
            sq (channelDual Phi.val Z (e i)) := fun i => by
        rw [Xm_apply]
        refine xc_eq f _ _ _ i _ fun j => ?_
        show opc Phi e f s e0 f0 s0 Z (Sum.inr (j, i)) = _
        simp only [opc, Sum.elim_inr]
        rw [sa_swap hsq, hsqf, inner_smul_left, Complex.conj_ofReal]
      have hQB := (Pm_quad B (Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι)
          (opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z))).unique
        ((lb_hasSum Phi (sq u) (sq v) e0 t B Z ht hB).congr_fun fun i => by rw [hx0 i])
      have hQA := (Pm_quad (rk u v) (Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι)
          (opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z))).unique
        ((la_hasSum e sq (channelDual Phi.val Z) hsq u v).congr_fun fun i => by rw [hx1 i])
      have hN0 : ‖Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι)
          (opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z)‖ ^ 2 =
          (boundedTracePair (Phi.val sigma.coefficients)
            (Z.comp (ContinuousLinearMap.adjoint Z))).re :=
        (Xm_sq f0 _ _ _).unique ((n_hasSum sJ e0 f0 s0 hs0' hs1' hfv' t ht htf Z).congr_fun
          fun i => by rw [← hx0 i]; rfl)
      have hN1 : ‖Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι)
          (opPair Phi e f s e0 f0 s0 hs0 hs1 hs0' hs1' Z)‖ ^ 2 =
          (boundedTracePair sigma.coefficients ((channelDual Phi.val Z).comp
            (ContinuousLinearMap.adjoint (channelDual Phi.val Z)))).re :=
        (Xm_sq f _ _ _).unique ((n_hasSum sigma e f s hs0 hs1 hfv sq hsq hsqf
          (channelDual Phi.val Z)).congr_fun fun i => by rw [← hx1 i]; rfl)
      rw [hQB, hQA, hN0, hN1]
      have hdb := defect_bound _ sq (defect_pos Phi Z) hsq f s hs0 hsqf
        (D_hasSum Phi sigma f s hs0 hs1 hfv Z) u v
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.comp_apply] at hdb
      exact hdb
    · exact (((Xm f0 _ _).continuous.inner ((Pm B).continuous.comp (Xm f0 _ _).continuous)).sub
        ((Xm f _ _).continuous.inner ((Pm (rk u v)).continuous.comp (Xm f _ _).continuous))).norm
    · exact continuous_const.mul (((continuous_norm.comp (Xm f0 _ _).continuous).pow 2).sub
        ((continuous_norm.comp (Xm f _ _).continuous).pow 2))
  have hRc := approx_mem Phi e f r s e0 f0 r0 s0 hr0 hr.summable hs0 hs1 hr0' hr'.summable
    hs0' hs1' happ
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at hRc
  have hmem := hsub hRc
  simp only [Set.mem_setOf_eq] at hmem
  set R : lp (fun _ : (κ0 × ι0) ⊕ (κ × ι) => ℂ) 2 :=
    ⟨Rc e f e0 f0 r r0, memℓ2 _ (Rc_sq e f e0 f0 r r0 hr0 hr.summable hr0' hr'.summable)⟩ with hR
  have hy0 : ∀ i, Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) R i =
      ((Real.sqrt (r0 i) : ℝ) : ℂ) • e0 i := fun i => by
    rw [Xm_apply]
    refine xc_eq f0 _ _ _ i _ fun j => ?_
    show Rc e f e0 f0 r r0 (Sum.inl (j, i)) = _
    simp only [Rc, Sum.elim_inl]
    rw [inner_smul_right, mul_comm]
  have hy1 : ∀ i, Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) R i =
      ((Real.sqrt (r i) : ℝ) : ℂ) • e i := fun i => by
    rw [Xm_apply]
    refine xc_eq f _ _ _ i _ fun j => ?_
    show Rc e f e0 f0 r r0 (Sum.inr (j, i)) = _
    simp only [Rc, Sum.elim_inr]
    rw [inner_smul_right, mul_comm]
  have hN0 : ‖Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) R‖ ^ 2 = 1 :=
    (Xm_sq f0 _ _ _).unique (hr'.congr_fun fun i => by
      show ‖Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) R i‖ ^ 2 = r0 i
      rw [hy0 i, smul_sq_norm e0 (hr0' i)])
  have hN1 : ‖Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) R‖ ^ 2 = 1 :=
    (Xm_sq f _ _ _).unique (hr.congr_fun fun i => by
      show ‖Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) R i‖ ^ 2 = r i
      rw [hy1 i, smul_sq_norm e (hr0 i)])
  have hQB := (Pm_quad B (Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) R)).tsum_eq
  have hQA := (Pm_quad (rk u v) (Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) R)).tsum_eq
  rw [hN0, hN1, sub_self, mul_zero, norm_le_zero_iff, sub_eq_zero, ← hQB, ← hQA] at hmem
  have e1 : ∀ i, ⟪Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) R i,
      B (Xm f0 (pi0 κ0 ι0 κ ι) (pi0_inj κ0 ι0 κ ι) R i)⟫_ℂ = (r0 i : ℂ) * ⟪e0 i, B (e0 i)⟫_ℂ :=
    fun i => by rw [hy0 i, smul_quad e0 B (hr0' i)]
  have e2 : ∀ i, ⟪Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) R i,
      rk u v (Xm f (pi1 κ0 ι0 κ ι) (pi1_inj κ0 ι0 κ ι) R i)⟫_ℂ =
        (r i : ℂ) * ⟪e i, rk u v (e i)⟫_ℂ :=
    fun i => by rw [hy1 i, smul_quad e (rk u v) (hr0 i)]
  rw [tsum_congr e1, tsum_congr e2] at hmem
  exact hmem

end Main

/-! ### Assembly of C4 -/

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

attribute [-instance] P45Petz.gfc0 P45Petz.gfc1 P45Petz.gfc2 P45Petz.gfc3 P45Petz.gfc4 P45Petz.gfc5 P45Petz.gfc6 P45Petz.gfc7 P45Petz.gsc0 P45Petz.gsc1 P45Petz.gsc2 P45Petz.gsc3 P45Petz.gsc4 P45Petz.gsc5 P45Petz.gsc6 P45Petz.gsc7 P45Petz.gsc8 P45Petz.gsc9 P45Petz.gsc10 P45Petz.gsc11 P45Petz.gsc12 P45Petz.gsc13 P45Petz.gsc14 P45Petz.gsc15 P45Petz.gsc16 P45Petz.gsc17 P45Petz.gsc18 P45Petz.gsc19 P45Petz.gsc20 P45Petz.gsc21 P45Petz.gsc22 P45Petz.gsc23 P45Petz.gsc24 P45Petz.gsc25 P45Petz.gsc26 P45Petz.gsc27 P45Petz.gsc28 P45Petz.hsc0 P45Petz.hsc1 P45Petz.hsc2 P45Petz.hsc3 P45Petz.hsc4 P45Petz.hsc5 P45Petz.hsc6 P45Petz.hsc7 P45Petz.hsc8 P45Petz.hsc9 P45Petz.hsc10 P45Petz.hsc11 P45Petz.hsc12 P45Petz.hsc13 P45Petz.hsc14 P45Petz.hsc15 P45Petz.hsc16 P45Petz.hsc17 P45Petz.hsc18 P45Petz.hsc19 P45Petz.hsc20 P45Petz.hsc21 P45Petz.hsc22 P45Petz.hsc23 P45Petz.hsc24 P45Petz.hsc25 P45Petz.hsc26 P45Petz.hsc27 P45Petz.hsc28 P45Petz.hsc29 P45Petz.osc0 P45Petz.osc1 P45Petz.osc2 P45Petz.osc3 P45Petz.osc4 P45Petz.osc5 P45Petz.osc6 P45Petz.osc7 P45Petz.osc8 P45Petz.osc9 P45Petz.osc10 P45Petz.osc11 P45Petz.osc12 P45Petz.osc13 P45Petz.osc14 P45Petz.osc15 P45Petz.osc16 P45Petz.osc17 P45Petz.osc18 P45Petz.osc19 P45Petz.osc20 P45Petz.osc21 P45Petz.osc22 P45Petz.osc23 P45Petz.hsc_t2 P45Petz.fsc0 P45Petz.fsc1 P45Petz.fsc2 P45Petz.fsc3 P45Petz.fsc4 P45Petz.fsc5

open QAlgorithms.Papers.Independent.Gap48.P45 QAlgorithms.RealRegisters QAlgorithms.Papers.Independent.Dependency50.P33 QAlgorithms.Papers.Independent.Frontier18.P01 QAlgorithms.Papers.Independent.Frontier18.P07 QAlgorithms.Papers.Independent.Frontier18.P18 in
theorem solution
    {I J : Type} [Countable I] [Countable J]
    (Phi : Channel I J) (rho sigma : State I)
    {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr : HasSum r 1)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr' : HasSum r0 1)
    (hev' : ∀ i, boundedOperator (Phi.val rho.coefficients) (e0 i) = (r0 i : ℂ) • e0 i)
    (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (hfv' : ∀ j, boundedOperator (Phi.val sigma.coefficients) (f0 j) = (s0 j : ℂ) • f0 j)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ Z : Hilbert J →L[ℂ] Hilbert J,
      (∑' p : κ0 × ι0, ‖(Real.sqrt (s0 p.1) : ℂ) * inner ℂ (f0 p.1) (Z (e0 p.2)) -
          inner ℂ (f0 p.1) (e0 p.2) * (Real.sqrt (r0 p.2) : ℂ)‖ ^ 2) +
      (∑' p : κ × ι, ‖(Real.sqrt (s p.1) : ℂ) * inner ℂ (f p.1) (channelDual Phi.val Z (e p.2)) -
          inner ℂ (f p.1) (e p.2) * (Real.sqrt (r p.2) : ℂ)‖ ^ 2) < ε)
    (t : Hilbert J →L[ℂ] Hilbert J) (ht : ContinuousLinearMap.adjoint t = t)
    (htf : ∀ j, t (f0 j) = ((Real.sqrt (s0 j) : ℝ) : ℂ) • f0 j)
    (sq : Hilbert I →L[ℂ] Hilbert I) (hsq : ContinuousLinearMap.adjoint sq = sq)
    (hsqf : ∀ j, sq (f j) = ((Real.sqrt (s j) : ℝ) : ℂ) • f j)
    (u v : Hilbert I) (B : Hilbert J →L[ℂ] Hilbert J)
    (hB : t.comp (B.comp t) =
      boundedOperator (Phi.val (operatorCoeff ((innerSL ℂ (sq v)).smulRight (sq u))))) :
    ∑' i, (r0 i : ℂ) * inner ℂ (e0 i) (B (e0 i)) =
      ∑' i, (r i : ℂ) * inner ℂ (e i) ((innerSL ℂ v).smulRight u (e i)) := by
  exact P45C4J.main_eq Phi rho sigma e f r s hr0 hr hev hs0 hs1 hfv e0 f0 r0 s0 hr0' hr' hev' hs0' hs1' hfv'
    happ t ht htf sq hsq hsqf u v B hB

end

end ChildRoot
