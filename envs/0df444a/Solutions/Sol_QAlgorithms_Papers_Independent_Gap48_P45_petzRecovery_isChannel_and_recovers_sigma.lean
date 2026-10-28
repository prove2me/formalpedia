-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.petzRecovery_isChannel_and_recovers_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T00:47:25.792141+00:00
-- url     : https://prove2.me/submissions/2ee0f992-d1f9-4b94-9c33-80c4b880ce21

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

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

lemma supp_fix {J : Type} (X : Matrix J J ℂ) :
    (ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection X).comp
      (boundedOperator X) = 0 := by
  ext1 x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
  rw [sub_eq_zero, eq_comm, coefficientSupportProjection, Submodule.starProjection_eq_self_iff]
  exact Submodule.le_topologicalClosure _ ⟨x, rfl⟩

lemma pair_drop {J : Type} (X : Matrix J J ℂ) (B : Hilbert J →L[ℂ] Hilbert J) (c : ℂ) :
    boundedTracePair X (B + c • (ContinuousLinearMap.id ℂ (Hilbert J) -
      coefficientSupportProjection X)) = boundedTracePair X B := by
  unfold boundedTracePair
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, supp_fix, smul_zero, add_zero]

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
theorem c1_recover {I J : Type} (Phi : Channel I J) (sigma : State I) :
    petzRecovery Phi.val sigma.coefficients (Phi.val sigma.coefficients) = sigma.coefficients := by
  funext i j
  set rho : State J := ⟨Phi.val sigma.coefficients,
    chan_density Phi.val Phi.property _ sigma.density⟩ with hrho
  obtain ⟨ht, htt, hHSt⟩ := sqrt_state rho
  obtain ⟨hs, hss, hHSs⟩ := sqrt_state sigma
  set t := positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) with htdef
  set s := positiveSquareRoot (boundedOperator sigma.coefficients) with hsdef
  set A := boundedOperator (Matrix.single j i (1 : ℂ)) with hAdef
  set a : ℕ → Hilbert I := fun k => bvec j + Complex.I ^ k • bvec i with hadef
  have hA : A = ∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) • rk (a k) (a k) := by
    rw [hAdef, unit_rk, unit_polar]
  have hex := good_sum Phi sigma 4 (fun k => Complex.I ^ k / 4) a
  rw [← hA] at hex
  unfold petzRecovery petzExtendedDual
  rw [petzSupportedDual, dif_pos hex]
  set B := hex.choose with hBdef
  have hB2 := hex.choose_spec.2
  rw [← hBdef] at hB2
  rw [pair_drop, tracePair_cyc (Phi.val sigma.coefficients) t B ht htt hHSt.summable]
  set Y := operatorCoeff (s.comp (A.comp s)) with hYdef
  have hYtc : IsTraceClass Y := by
    have hsA : s.comp ((∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) • rk (a k) (a k)).comp s) =
        ∑ k ∈ Finset.range 4, (Complex.I ^ k / 4) • rk (s (a k)) (s (a k)) := by
      ext1 x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, map_sum, map_smul, rk_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← ContinuousLinearMap.adjoint_inner_left, hs]
    rw [hYdef, hA, hsA, coeff_sum]
    simp_rw [coeff_smul]
    exact tc_sum 4 _ (fun k => operatorCoeff (rk (s (a k)) (s (a k)))) (fun k => tc_rk _ _)
  have e1 : ∀ k, inner ℂ (t (bvec k)) (B (t (bvec k))) = Phi.val Y k k := by
    intro k
    rw [← sa_swap ht]
    have h := congrArg (fun F : Hilbert J →L[ℂ] Hilbert J => F (bvec k)) hB2
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, inner_bvec_left]
    have h2 := congrFun (congrFun (coeff_bO (Phi.property.1 _ hYtc)) k) k
    rw [← h2, operatorCoeff_apply]
    rfl
  rw [tsum_congr e1]
  obtain ⟨τ, h1, h2⟩ := chan_trace Phi hYtc
  rw [h2.tsum_eq, ← h1.tsum_eq]
  have e2 : ∀ k, Y k k = inner ℂ (s (bvec k)) (A (s (bvec k))) := by
    intro k
    rw [hYdef, operatorCoeff_apply, show (lp.single 2 k (1 : ℂ) : Hilbert I) = bvec k from rfl,
      coord_eq_inner, ContinuousLinearMap.comp_apply, sa_swap hs, ContinuousLinearMap.comp_apply]
  rw [tsum_congr e2, ← hs_cyc s A hs hHSs.summable]
  have e3 : ∀ x, inner ℂ (bvec x) (A (s (s (bvec x)))) =
      sigma.coefficients i x * (bvec j : Hilbert I) x := by
    intro x
    have hss' : s (s (bvec x)) = boundedOperator sigma.coefficients (bvec x) := by
      rw [← hss]; rfl
    rw [hss', hAdef, unit_rk, rk_apply, inner_smul_right, inner_bvec_left, inner_bvec_left]
    have h3 := congrFun (congrFun (coeff_bO sigma.density.1) i) x
    rw [← h3, operatorCoeff_apply]
    rfl
  rw [tsum_congr e3, tsum_eq_single j]
  · simp [bvec]
  · intro x hx
    simp [bvec, lp.single_apply, Pi.single_apply, hx]

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

theorem theta_add {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (sigma : Matrix I I ℂ)
    {X Y : Matrix J J ℂ} (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    petzRecovery Phi sigma (X + Y) = petzRecovery Phi sigma X + petzRecovery Phi sigma Y := by
  funext i j
  simp only [petzRecovery, Matrix.add_apply]
  exact pair_add _ hX hY

theorem theta_smul {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (sigma : Matrix I I ℂ)
    (c : ℂ) {X : Matrix J J ℂ} (hX : IsTraceClass X) :
    petzRecovery Phi sigma (c • X) = c • petzRecovery Phi sigma X := by
  funext i j
  simp only [petzRecovery, Matrix.smul_apply]
  exact pair_smul _ c hX

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

open scoped ComplexOrder in
lemma inner_self_nonneg_c {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : E) :
    0 ≤ inner ℂ v v := by
  rw [Complex.nonneg_iff]
  refine ⟨?_, (inner_self_im (𝕜 := ℂ) v).symm⟩
  have := inner_self_nonneg (𝕜 := ℂ) (x := v)
  simpa using this

open scoped ComplexOrder in
/-- Schur product of two Gram matrices is positive. -/
lemma gram_schur {ι T U : Type} (s : Finset ι) (x : ι → Hilbert T) (y : ι → Hilbert U) :
    0 ≤ ∑ p ∈ s, ∑ q ∈ s, inner ℂ (x p) (x q) * inner ℂ (y q) (y p) := by
  have hsum : ∀ p q, HasSum (fun k => star (x p k) * x q k) (inner ℂ (x p) (x q)) := by
    intro p q
    have h := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : T => ℂ) (x p) (x q)
    have heq : (fun k => star (x p k) * x q k) = fun k => inner ℂ ((x p) k) ((x q) k) := by
      funext k
      simp [RCLike.inner_apply, mul_comm]
    rw [heq]
    exact h
  have hk : ∀ p q, HasSum (fun k => star (x p k) * x q k * inner ℂ (y q) (y p))
      (inner ℂ (x p) (x q) * inner ℂ (y q) (y p)) := fun p q => (hsum p q).mul_right _
  have htot : HasSum (fun k => ∑ p ∈ s, ∑ q ∈ s, star (x p k) * x q k * inner ℂ (y q) (y p))
      (∑ p ∈ s, ∑ q ∈ s, inner ℂ (x p) (x q) * inner ℂ (y q) (y p)) :=
    hasSum_sum (fun p _ => hasSum_sum (fun q _ => hk p q))
  rw [← htot.tsum_eq]
  refine tsum_nonneg (fun k => ?_)
  set v : Hilbert U := ∑ p ∈ s, star (x p k) • y p with hv
  have hvv : inner ℂ v v = ∑ p ∈ s, ∑ q ∈ s, star (x p k) * x q k * inner ℂ (y q) (y p) := by
    rw [hv, sum_inner, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [inner_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [inner_smul_left, inner_smul_right]
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  rw [← hvv]
  exact inner_self_nonneg_c v

lemma form_eq2 {T : Type} (S : Hilbert T →L[ℂ] Hilbert T) (F : Finset T) (w v : T → ℂ) :
    inner ℂ (∑ p ∈ F, w p • (lp.single 2 p (1:ℂ) : Hilbert T))
        (S (∑ q ∈ F, v q • (lp.single 2 q (1:ℂ) : Hilbert T))) =
      ∑ p ∈ F, ∑ q ∈ F, star (w p) * operatorCoeff S p q * v q := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, inner_smul_left, inner_smul_right, operatorCoeff_apply, lp.inner_single_left]
  simp
  ring

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

open scoped ComplexOrder in
/-- Complete positivity of a channel, finite form, unit amplified vector. -/
lemma cp_unit {I J : Type} (Phi : Channel I J) (n : ℕ) (x : Fin n → Hilbert I)
    (hx : ‖amp x‖ = 1) (F : Finset J) (c : Fin n → J → ℂ) :
    0 ≤ ∑ a, ∑ b, inner ℂ (∑ j ∈ F, c a j • (lp.single 2 j (1:ℂ) : Hilbert J))
      (boundedOperator (Phi.val (operatorCoeff (rk (x a) (x b))))
        (∑ j ∈ F, c b j • (lp.single 2 j (1:ℂ) : Hilbert J))) := by
  set ξ := amp x with hξdef
  have hρ := isDensity_rk ξ hx
  have hout := (Phi.property.2.2.2 n ⟨_, hρ⟩).2.1 (F ×ˢ Finset.univ) (fun p => c p.2 p.1)
  have hblk : ∀ a b, (fun i i' => (operatorCoeff (rk ξ ξ)) (i, a) (i', b)) =
      operatorCoeff (rk (x a) (x b)) := by
    intro a b; funext i i'; rw [coeff_rk, coeff_rk]; rfl
  have htc : ∀ a b, IsTraceClass (Phi.val (operatorCoeff (rk (x a) (x b)))) :=
    fun a b => Phi.property.1 _ (tc_rk _ _)
  have hform : (∑ a, ∑ b, inner ℂ (∑ j ∈ F, c a j • (lp.single 2 j (1:ℂ) : Hilbert J))
      (boundedOperator (Phi.val (operatorCoeff (rk (x a) (x b))))
        (∑ j ∈ F, c b j • (lp.single 2 j (1:ℂ) : Hilbert J)))) =
      ∑ p ∈ F ×ˢ Finset.univ, ∑ q ∈ F ×ˢ Finset.univ, star (c p.2 p.1) *
        tensorApply Phi.val (operatorCoeff (rk ξ ξ)) p q * c q.2 q.1 := by
    simp only [tensorApply, hblk, Finset.sum_product]
    simp_rw [form_eq2, coeff_bO (htc _ _)]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact (Finset.sum_congr rfl (fun j _ => Finset.sum_comm)).trans Finset.sum_comm
  rw [hform]
  exact Complex.nonneg_iff.mpr ⟨hout.2, hout.1.symm⟩


lemma bO_zero {T : Type} : boundedOperator (0 : Matrix T T ℂ) = 0 :=
  bO_eq (by funext i j; simp [operatorCoeff])

lemma rk_smul_smul {T : Type} (c : ℂ) (u v : Hilbert T) :
    rk (c • u) (c • v) = (c * star c) • rk u v := by
  ext1 x
  simp only [rk_apply, ContinuousLinearMap.smul_apply, inner_smul_left, smul_smul]
  congr 1
  simp only [Complex.star_def]
  ring

open scoped ComplexOrder in
/-- Complete positivity of a channel, finite form. -/
lemma cp_fin {I J : Type} (Phi : Channel I J) (n : ℕ) (x : Fin n → Hilbert I)
    (F : Finset J) (c : Fin n → J → ℂ) :
    0 ≤ ∑ a, ∑ b, inner ℂ (∑ j ∈ F, c a j • (lp.single 2 j (1:ℂ) : Hilbert J))
      (boundedOperator (Phi.val (operatorCoeff (rk (x a) (x b))))
        (∑ j ∈ F, c b j • (lp.single 2 j (1:ℂ) : Hilbert J))) := by
  set N := ‖amp x‖ with hN
  rcases (norm_nonneg (amp x)).lt_or_eq with hpos | hzero
  · set k : ℂ := ((N⁻¹ : ℝ) : ℂ) with hk
    set x' : Fin n → Hilbert I := fun a => k • x a with hx'
    have hamp : amp x' = k • amp x := lp.ext (funext fun p => rfl)
    have hn1 : ‖amp x'‖ = 1 := by
      rw [hamp, norm_smul, hk, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos), ← hN, inv_mul_cancel₀ hpos.ne']
    have h := cp_unit Phi n x' hn1 F c
    have hkk : k * star k = (((N ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [hk, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1; rw [sq, mul_inv]
    have hterm : ∀ a b, boundedOperator (Phi.val (operatorCoeff (rk (x' a) (x' b)))) =
        (((N ^ 2)⁻¹ : ℝ) : ℂ) • boundedOperator (Phi.val (operatorCoeff (rk (x a) (x b)))) := by
      intro a b
      rw [hx', rk_smul_smul, hkk, coeff_smul, Phi.property.2.2.1 _ _ (tc_rk _ _),
        bO_smul _ (Phi.property.1 _ (tc_rk _ _))]
    simp_rw [hterm, ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum] at h
    have hr : 0 < (N ^ 2)⁻¹ := inv_pos.mpr (pow_pos hpos 2)
    rw [Complex.nonneg_iff] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [Complex.re_ofReal_mul] at h1
    rw [Complex.im_ofReal_mul] at h2
    exact ⟨(mul_nonneg_iff_of_pos_left hr).mp h1,
      ((mul_eq_zero.mp h2.symm).resolve_left hr.ne').symm⟩
  · have hx0 : ∀ a, x a = 0 := by
      intro a
      have h0 : amp x = 0 := norm_eq_zero.mp hzero.symm
      exact lp.ext (funext fun i => by
        have := congrArg (fun v : Hilbert (I × Fin n) => v (i, a)) h0
        simpa [amp] using this)
    have hrk : ∀ a b, rk (x a) (x b) = 0 := by
      intro a b; rw [hx0 a, hx0 b]; ext1 v; simp [rk_apply]
    have hc0 : operatorCoeff (0 : Hilbert I →L[ℂ] Hilbert I) = 0 := by
      funext i j; simp [operatorCoeff]
    simp [hrk, hc0, chan_zero, bO_zero]

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

open scoped ComplexOrder in
/-- Complete positivity of a channel against arbitrary vectors. -/
lemma cp_all {I J : Type} (Phi : Channel I J) (n : ℕ) (x : Fin n → Hilbert I)
    (γ : Fin n → Hilbert J) :
    0 ≤ ∑ a, ∑ b, inner ℂ (γ a)
      (boundedOperator (Phi.val (operatorCoeff (rk (x a) (x b)))) (γ b)) := by
  have hg : ∀ a, Tendsto (fun F : Finset J => ∑ j ∈ F, γ a j • (lp.single 2 j (1:ℂ) : Hilbert J))
      atTop (𝓝 (γ a)) := fun a => hasSum_basis (γ a)
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun a _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun b _ => Filter.Tendsto.inner (𝕜 := ℂ) (hg a)
      (((boundedOperator (Phi.val (operatorCoeff (rk (x a) (x b))))).continuous.tendsto _).comp
        (hg b))))
  refine ge_of_tendsto' hlim (fun F => ?_)
  exact cp_fin Phi n x F (fun a j => γ a j)

open scoped ComplexOrder in
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- U3b, supported part, finite index. -/
lemma u3b_B_fin {I J : Type} (Phi : Channel I J) (sigma : State I) (n : ℕ)
    (α : Fin n → Hilbert I) (β : Fin n → Hilbert J) :
    0 ≤ ∑ a, ∑ b, inner ℂ (β a)
      (petzSupportedDual Phi.val sigma.coefficients (rk (α a) (α b)) (β b)) := by
  set rho : State J := ⟨Phi.val sigma.coefficients,
    chan_density Phi.val Phi.property _ sigma.density⟩ with hrho
  have hta : ContinuousLinearMap.adjoint (positiveSquareRoot (boundedOperator
      (Phi.val sigma.coefficients))) = positiveSquareRoot (boundedOperator
      (Phi.val sigma.coefficients)) := (sqrt_state rho).1
  have htt : positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) *
      positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) =
      boundedOperator (Phi.val sigma.coefficients) := (sqrt_state rho).2.1
  have hspec := fun a b => dual_rk Phi sigma (α a) (α b)
  have hSsa : ∀ x y : Hilbert J,
      inner ℂ x (coefficientSupportProjection (Phi.val sigma.coefficients) y) =
      inner ℂ (coefficientSupportProjection (Phi.val sigma.coefficients) x) y :=
    fun x y => (Submodule.inner_starProjection_left_eq_right _ x y).symm
  have hmemK : ∀ x : Hilbert J, coefficientSupportProjection (Phi.val sigma.coefficients) x ∈
      ((LinearMap.range (boundedOperator (Phi.val sigma.coefficients)).toLinearMap).topologicalClosure
        : Set (Hilbert J)) := fun x => Submodule.starProjection_apply_mem _ x
  set S := coefficientSupportProjection (Phi.val sigma.coefficients) with hS
  set P := boundedOperator (Phi.val sigma.coefficients) with hP
  set t := positiveSquareRoot P with ht
  set D := petzSupportedDual Phi.val sigma.coefficients with hD
  set sq := positiveSquareRoot (boundedOperator sigma.coefficients) with hsq
  have h1 : ∀ a b, inner ℂ (β a) (D (rk (α a) (α b)) (β b)) =
      inner ℂ (S (β a)) (D (rk (α a) (α b)) (S (β b))) := by
    intro a b
    conv_lhs => rw [← (hspec a b).1]
    simp only [ContinuousLinearMap.comp_apply]
    exact hSsa _ _
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))]
  have happrox : ∀ a, ∃ y : ℕ → Hilbert J, Tendsto (fun m => t (y m)) atTop (𝓝 (S (β a))) := by
    intro a
    have hmem : S (β a) ∈ closure (Set.range t) := K_sub t P htt (hmemK (β a))
    obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
    choose y hy using hx
    refine ⟨y, ?_⟩
    have hxy : (fun m => t (y m)) = x := funext hy
    rw [hxy]; exact hlim
  choose y hy using happrox
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun a _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun b _ => Filter.Tendsto.inner (𝕜 := ℂ) (hy a)
      (((D (rk (α a) (α b))).continuous.tendsto _).comp (hy b))))
  refine ge_of_tendsto' hlim (fun m => ?_)
  have h2 : ∀ a b, inner ℂ (t (y a m)) (D (rk (α a) (α b)) (t (y b m))) =
      inner ℂ (y a m) (boundedOperator (Phi.val (operatorCoeff (rk (sq (α a)) (sq (α b)))))
        (y b m)) := by
    intro a b
    rw [← sa_swap hta, ← (hspec a b).2]
    rfl
  simp only [Function.comp]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h2 a b))]
  exact cp_all Phi n (fun a => sq (α a)) (fun a => y a m)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- Tr(sigma rk(u,v)) = <s v, s u>. -/
lemma sig_pair {T : Type} (sigma : State T) (u v : Hilbert T) :
    boundedTracePair sigma.coefficients (rk u v) =
      inner ℂ (positiveSquareRoot (boundedOperator sigma.coefficients) v)
        (positiveSquareRoot (boundedOperator sigma.coefficients) u) := by
  obtain ⟨hr, _, hsum⟩ := sqrt_state sigma
  set rs := positiveSquareRoot (boundedOperator sigma.coefficients) with hrs
  have h := pair_gen (rk u v) (fun k => rs (bvec k)) (fun k => rs (bvec k))
    (hsum.summable.congr (fun k => sq _)) (fun i j => dens_exp sigma i j)
  refine h.unique ?_
  refine HasSum.congr_fun (lp.hasSum_inner (𝕜 := ℂ) (rs v) (rs u)) (fun k => ?_)
  rw [rk_apply, inner_smul_right, sa_swap hr v (bvec k), ← sa_swap hr (bvec k) u,
    inner_bvec_left]
  unfold bvec
  rw [inner_single_right']
  simp [RCLike.inner_apply, mul_comm]

lemma proj_compl_inner {T : Type} (X : Matrix T T ℂ) (x y : Hilbert T) :
    inner ℂ x ((ContinuousLinearMap.id ℂ (Hilbert T) - coefficientSupportProjection X) y) =
      inner ℂ ((ContinuousLinearMap.id ℂ (Hilbert T) - coefficientSupportProjection X) x)
        ((ContinuousLinearMap.id ℂ (Hilbert T) - coefficientSupportProjection X) y) := by
  unfold coefficientSupportProjection
  set K := (LinearMap.range (boundedOperator X).toLinearMap).topologicalClosure
  have hid : K.starProjection (K.starProjection y) = K.starProjection y := by
    have := (Submodule.isIdempotentElem_starProjection K).eq
    exact congrArg (fun f : Hilbert T →L[ℂ] Hilbert T => f y) this
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_sub_left,
    inner_sub_right]
  rw [Submodule.inner_starProjection_left_eq_right K x y,
    Submodule.inner_starProjection_left_eq_right K x (K.starProjection y), hid]
  ring

open scoped ComplexOrder in
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- U3b, off-support part, finite index (Schur product of two Gram matrices). -/
lemma u3b_sig_fin {I J : Type} (sigma : State I) (X : Matrix J J ℂ) (n : ℕ)
    (α : Fin n → Hilbert I) (β : Fin n → Hilbert J) :
    0 ≤ ∑ a, ∑ b, inner ℂ (β a)
      ((boundedTracePair sigma.coefficients (rk (α a) (α b)) •
        (ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection X)) (β b)) := by
  have h : ∀ a b, inner ℂ (β a)
      ((boundedTracePair sigma.coefficients (rk (α a) (α b)) •
        (ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection X)) (β b)) =
      inner ℂ (positiveSquareRoot (boundedOperator sigma.coefficients) (α b))
        (positiveSquareRoot (boundedOperator sigma.coefficients) (α a)) *
      inner ℂ ((ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection X) (β a))
        ((ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection X) (β b)) := by
    intro a b
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, sig_pair, proj_compl_inner]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h a b)), Finset.sum_comm]
  exact gram_schur Finset.univ (fun a => positiveSquareRoot (boundedOperator sigma.coefficients) (α a))
    (fun a => (ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection X) (β a))

open scoped ComplexOrder in
/-- U3b: the extended Petz dual is completely positive on rank-one families. -/
lemma u3b {I J ι : Type} (Phi : Channel I J) (sigma : State I) (s : Finset ι)
    (α : ι → Hilbert I) (β : ι → Hilbert J) :
    0 ≤ ∑ p ∈ s, ∑ q ∈ s, inner ℂ (β p)
      (petzExtendedDual Phi.val sigma.coefficients (rk (α p) (α q)) (β q)) := by
  have hs2 : ∀ G : ι → ℂ, ∑ p ∈ s, G p = ∑ i : Fin s.card, G (s.equivFin.symm i) := by
    intro G
    rw [← Finset.sum_coe_sort s G]
    exact (s.equivFin.symm.sum_comp (fun p : s => G p)).symm
  simp_rw [hs2]
  have hB := u3b_B_fin Phi sigma s.card (fun i => α (s.equivFin.symm i))
    (fun i => β (s.equivFin.symm i))
  have hS := u3b_sig_fin sigma (Phi.val sigma.coefficients) s.card
    (fun i => α (s.equivFin.symm i)) (fun i => β (s.equivFin.symm i))
  have := add_nonneg hB hS
  simp only [← Finset.sum_add_distrib, ← inner_add_right, ← ContinuousLinearMap.add_apply] at this
  simpa only [petzExtendedDual] using this

open scoped ComplexOrder in
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- Clause 4 forms: every amplification of the Petz recovery map has positive finite forms. -/
lemma theta_forms {I J A : Type} (Phi : Channel I J) (sigma : State I) (rho : State (J × A)) :
    PSDForms (tensorApply (petzRecovery Phi.val sigma.coefficients) rho.coefficients) := by
  intro s z
  set D := petzExtendedDual Phi.val sigma.coefficients with hD
  set r := positiveSquareRoot (boundedOperator rho.coefficients) with hr
  set M := tensorApply (petzRecovery Phi.val sigma.coefficients) rho.coefficients with hM
  have hent : ∀ P Q : I × A, HasSum (fun k => inner ℂ (slice (r (bvec k)) Q.2)
      (D (rk (bvec Q.1) (bvec P.1)) (slice (r (bvec k)) P.2))) (M P Q) := by
    intro P Q
    have := block_pair rho P.2 Q.2 (D (rk (bvec Q.1) (bvec P.1)))
    simpa only [hM, tensorApply, petzRecovery, unit_rk] using this
  have hF : HasSum (fun k => ∑ P ∈ s, ∑ Q ∈ s, star (z P) *
      inner ℂ (slice (r (bvec k)) Q.2) (D (rk (bvec Q.1) (bvec P.1)) (slice (r (bvec k)) P.2)) * z Q)
      (∑ P ∈ s, ∑ Q ∈ s, star (z P) * M P Q * z Q) := by
    refine hasSum_sum (fun P _ => hasSum_sum (fun Q _ => ?_))
    exact ((hent P Q).mul_left (star (z P))).mul_right (z Q)
  have hk : ∀ k, 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, star (z P) *
      inner ℂ (slice (r (bvec k)) Q.2) (D (rk (bvec Q.1) (bvec P.1)) (slice (r (bvec k)) P.2)) * z Q := by
    intro k
    have h := u3b Phi sigma s (fun P => bvec P.1) (fun P => star (z P) • slice (r (bvec k)) P.2)
    rw [Finset.sum_comm]
    refine le_of_le_of_eq h (Finset.sum_congr rfl (fun Q _ => Finset.sum_congr rfl (fun P _ => ?_)))
    simp only [inner_smul_left, inner_smul_right, map_smul, starRingEnd_apply, star_star, hD]
    ring
  have h0 : 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, star (z P) * M P Q * z Q := hF.nonneg hk
  rw [Complex.nonneg_iff] at h0
  exact ⟨h0.2.symm, h0.1⟩

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

lemma mat_form {I J : Type} (Phi : Channel I J) (w : ℕ → Hilbert I)
    (hw : Summable (fun n => ‖w n‖ ^ 2)) (g : Hilbert J) :
    (inner ℂ g (boundedOperator (Phi.val (Mat w)) g)).im = 0 ∧
    0 ≤ (inner ℂ g (boundedOperator (Phi.val (Mat w)) g)).re ∧
    (inner ℂ g (boundedOperator (Phi.val (Mat w)) g)).re ≤ (∑' n, ‖w n‖ ^ 2) * ‖g‖ ^ 2 := by
  by_cases h0 : (∑' n, ‖w n‖ ^ 2) = 0
  · have hf := (hasSum_zero_iff_of_nonneg (fun n => sq_nonneg ‖w n‖)).mp (h0 ▸ hw.hasSum)
    have hw0 : ∀ n, w n = 0 := fun n => by
      have := congrFun hf n
      simpa using this
    have hM : Mat w = 0 := by funext i j; simp [Mat, hw0]
    rw [hM, chan_zero, bO_zero, h0]
    simp
  · have hτ : 0 < ∑' n, ‖w n‖ ^ 2 :=
      lt_of_le_of_ne (tsum_nonneg (fun _ => sq_nonneg _)) (Ne.symm h0)
    have hd := chan_density Phi.val Phi.property _ (isDensity_mat w hw h0)
    obtain ⟨a, b, c⟩ := dens_form ⟨_, hd⟩ g
    have hlin := Phi.property.2.2.1 (((∑' n, ‖w n‖ ^ 2)⁻¹ : ℝ) : ℂ) (Mat w) (tc_mat w hw)
    simp only [hlin, bO_smul _ (Phi.property.1 _ (tc_mat w hw)), ContinuousLinearMap.smul_apply,
      inner_smul_right, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero] at a b c
    refine ⟨(mul_eq_zero.mp a).resolve_left (inv_ne_zero h0),
      (mul_nonneg_iff_of_pos_left (inv_pos.mpr hτ)).mp b, ?_⟩
    rw [inv_mul_le_iff₀ hτ] at c
    exact c

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

lemma hasSum_off {α M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (f : α → M) {a : M} (h : HasSum f a) (F : Finset α) :
    HasSum (fun i => if i ∈ F then 0 else f i) (a - ∑ i ∈ F, f i) := by
  classical
  have h2 : HasSum (fun i => if i ∈ F then f i else 0) (∑ i ∈ F, f i) := by
    have : HasSum (fun i => if i ∈ F then f i else 0) (∑ i ∈ F, if i ∈ F then f i else 0) :=
      hasSum_sum_of_ne_finset_zero (fun i hi => if_neg hi)
    rwa [Finset.sum_congr rfl (fun i hi => if_pos hi)] at this
  refine (h.sub h2).congr_fun (fun i => ?_)
  by_cases hi : i ∈ F <;> simp [hi]

lemma ext_map {α β γ : Type} [Zero β] [Zero γ] {enc : α → ℕ} (henc : Function.Injective enc)
    (u : α → β) (φ : β → γ) (h0 : φ 0 = 0) (n : ℕ) :
    φ (Function.extend enc u 0 n) = Function.extend enc (fun i => φ (u i)) 0 n := by
  by_cases hn : ∃ i, enc i = n
  · obtain ⟨i, rfl⟩ := hn
    simp only [henc.extend_apply]
  · simp only [Function.extend_apply' _ _ _ hn, Pi.zero_apply, h0]

/-- The output of a channel minus its partial sums over a rank-one expansion of the input. -/
def tailOp {I J : Type} (Phi : Channel I J) (X : Matrix I I ℂ) (v : I → Hilbert I)
    (F : Finset I) : Hilbert J →L[ℂ] Hilbert J :=
  boundedOperator (Phi.val X) - ∑ i ∈ F, boundedOperator (Phi.val (operatorCoeff (rk (v i) (v i))))

lemma tail_le {I J : Type} [Countable I] (Phi : Channel I J) (X : Matrix I I ℂ)
    (v : I → Hilbert I) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (hXv : ∀ p q, HasSum (fun i => v i p * star (v i q)) (X p q)) (F : Finset I) (g : Hilbert J) :
    (inner ℂ g (tailOp Phi X v F g)).im = 0 ∧ 0 ≤ (inner ℂ g (tailOp Phi X v F g)).re ∧
    (inner ℂ g (tailOp Phi X v F g)).re ≤ (∑' i, ‖v i‖ ^ 2 - ∑ i ∈ F, ‖v i‖ ^ 2) * ‖g‖ ^ 2 := by
  classical
  obtain ⟨enc, henc⟩ := exists_injective_nat I
  set u : I → Hilbert I := fun i => if i ∈ F then 0 else v i with hu
  set w : ℕ → Hilbert I := Function.extend enc u 0 with hw
  have hn2 : HasSum (fun n => ‖w n‖ ^ 2) (∑' i, ‖v i‖ ^ 2 - ∑ i ∈ F, ‖v i‖ ^ 2) := by
    have e : (fun n => ‖w n‖ ^ 2) = Function.extend enc (fun i => ‖u i‖ ^ 2) 0 :=
      funext (fun n => ext_map henc u (fun x : Hilbert I => ‖x‖ ^ 2) (by simp) n)
    rw [e, hasSum_extend_zero henc]
    refine (hasSum_off _ hv.hasSum F).congr_fun (fun i => ?_)
    by_cases hi : i ∈ F <;> simp [hu, hi]
  have hw' : Summable (fun n => ‖w n‖ ^ 2) := hn2.summable
  have hM : Mat w = X - operatorCoeff (∑ i ∈ F, rk (v i) (v i)) := by
    funext p q
    have h1 : HasSum (fun n => w n p * star (w n q)) (X p q - ∑ i ∈ F, v i p * star (v i q)) := by
      have e : (fun n => w n p * star (w n q)) =
          Function.extend enc (fun i => u i p * star (u i q)) 0 :=
        funext (fun n => ext_map henc u (fun x : Hilbert I => x p * star (x q)) (by simp) n)
      rw [e, hasSum_extend_zero henc]
      refine (hasSum_off _ (hXv p q) F).congr_fun (fun i => ?_)
      by_cases hi : i ∈ F <;> simp [hu, hi]
    rw [Mat, h1.tsum_eq, Matrix.sub_apply, coeff_sum, Matrix.sum_apply]
    simp only [coeff_rk]
  have htc : ∀ i, IsTraceClass (operatorCoeff (rk (v i) (v i))) := fun i => tc_rk _ _
  have hX' : X = Mat w + ∑ i ∈ F, operatorCoeff (rk (v i) (v i)) := by
    rw [hM, coeff_sum, sub_add_cancel]
  have hT : tailOp Phi X v F = boundedOperator (Phi.val (Mat w)) := by
    unfold tailOp
    rw [hX', Phi.property.2.1 _ _ (tc_mat w hw') (tc_fsum _ _ htc), (chan_fsum Phi F _ htc).2,
      bO_add (Phi.property.1 _ (tc_mat w hw')) (tc_fsum _ _ (fun i => Phi.property.1 _ (htc i))),
      bO_fsum _ _ (fun i => Phi.property.1 _ (htc i)), add_sub_cancel_right]
  rw [hT, ← hn2.tsum_eq]
  exact mat_form Phi w hw' g

/-- The supported dual on the i-th diagonal matrix unit. -/
def Bi {I J : Type} (Phi : Channel I J) (sigma : State I) (i : I) : Hilbert J →L[ℂ] Hilbert J :=
  petzSupportedDual Phi.val sigma.coefficients (rk (bvec i) (bvec i))

/-- Support projection minus the partial sums of the diagonal supported duals. -/
def TF {I J : Type} (Phi : Channel I J) (sigma : State I) (F : Finset I) :
    Hilbert J →L[ℂ] Hilbert J :=
  coefficientSupportProjection (Phi.val sigma.coefficients) - ∑ i ∈ F, Bi Phi sigma i

open scoped ComplexOrder in
lemma bi_pos {I J : Type} (Phi : Channel I J) (sigma : State I) (i : I) (x : Hilbert J) :
    0 ≤ inner ℂ x (Bi Phi sigma i x) := by
  have h := u3b_B_fin Phi sigma 1 (fun _ => bvec i) (fun _ => x)
  simpa [Bi] using h

lemma S_idem {J : Type} (X : Matrix J J ℂ) (x : Hilbert J) :
    coefficientSupportProjection X (coefficientSupportProjection X x) =
      coefficientSupportProjection X x :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ x)

lemma S_sa {J : Type} (X : Matrix J J ℂ) (x y : Hilbert J) :
    inner ℂ x (coefficientSupportProjection X y) = inner ℂ (coefficientSupportProjection X x) y :=
  (Submodule.inner_starProjection_left_eq_right _ x y).symm

lemma TF_S {I J : Type} (Phi : Channel I J) (sigma : State I) (F : Finset I) (x : Hilbert J) :
    inner ℂ x (TF Phi sigma F x) =
      inner ℂ (coefficientSupportProjection (Phi.val sigma.coefficients) x)
        (TF Phi sigma F (coefficientSupportProjection (Phi.val sigma.coefficients) x)) := by
  set S := coefficientSupportProjection (Phi.val sigma.coefficients) with hS
  have hB : ∀ i (y : Hilbert J), Bi Phi sigma i y = S (Bi Phi sigma i (S y)) := fun i y => by
    have := congrArg (fun T => T y) (dual_rk Phi sigma (bvec i) (bvec i)).1
    simpa [Bi] using this.symm
  simp only [TF, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, inner_sub_right,
    inner_sum]
  congr 1
  · rw [S_idem]
    conv_lhs => rw [← S_idem (Phi.val sigma.coefficients) x]
    exact S_sa _ _ _
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hB i x]
    exact S_sa _ _ _

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
lemma TF_t {I J : Type} (Phi : Channel I J) (sigma : State I) (F : Finset I) (y : Hilbert J) :
    inner ℂ (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) y)
      (TF Phi sigma F (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) y)) =
    inner ℂ y (tailOp Phi sigma.coefficients
      (fun i => positiveSquareRoot (boundedOperator sigma.coefficients) (bvec i)) F y) := by
  set rho : State J := ⟨Phi.val sigma.coefficients,
    chan_density Phi.val Phi.property _ sigma.density⟩ with hrho
  have hta : ContinuousLinearMap.adjoint (positiveSquareRoot (boundedOperator
      (Phi.val sigma.coefficients))) = positiveSquareRoot (boundedOperator
      (Phi.val sigma.coefficients)) := (sqrt_state rho).1
  have htt : positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) *
      positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) =
      boundedOperator (Phi.val sigma.coefficients) := (sqrt_state rho).2.1
  set P := boundedOperator (Phi.val sigma.coefficients) with hP
  set t := positiveSquareRoot P with ht
  have hSt : coefficientSupportProjection (Phi.val sigma.coefficients) (t y) = t y :=
    Submodule.starProjection_eq_self_iff.mpr (mem_K t P hta htt y)
  simp only [TF, tailOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    inner_sub_right, inner_sum, hSt]
  congr 1
  · rw [← sa_swap hta, ← ContinuousLinearMap.mul_apply, htt]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← sa_swap hta]
    have h2 := (dual_rk Phi sigma (bvec i) (bvec i)).2
    rw [← h2]
    rfl

open scoped ComplexOrder in
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
lemma TF_pos {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I) (F : Finset I)
    (x : Hilbert J) : 0 ≤ inner ℂ x (TF Phi sigma F x) := by
  set rho : State J := ⟨Phi.val sigma.coefficients,
    chan_density Phi.val Phi.property _ sigma.density⟩ with hrho
  have htt : positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) *
      positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) =
      boundedOperator (Phi.val sigma.coefficients) := (sqrt_state rho).2.1
  set S := coefficientSupportProjection (Phi.val sigma.coefficients) with hS
  set P := boundedOperator (Phi.val sigma.coefficients) with hP
  set t := positiveSquareRoot P with ht
  rw [TF_S]
  have hmem : S x ∈ closure (Set.range t) :=
    K_sub t P htt (Submodule.starProjection_apply_mem _ x)
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose y hy using hz
  have hxy : (fun m => t (y m)) = z := funext hy
  rw [← hxy] at hlim
  have hl := Filter.Tendsto.inner (𝕜 := ℂ) hlim (((TF Phi sigma F).continuous.tendsto _).comp hlim)
  refine ge_of_tendsto' hl (fun m => ?_)
  simp only [Function.comp]
  rw [TF_t]
  obtain ⟨h1, h2, _⟩ := tail_le Phi sigma.coefficients _ (sqrt_state sigma).2.2.summable
    (fun p q => dens_exp sigma p q) F (y m)
  exact Complex.nonneg_iff.mpr ⟨h2, h1.symm⟩

open scoped ComplexOrder in
lemma TF_le {I J : Type} (Phi : Channel I J) (sigma : State I) (F : Finset I) (x : Hilbert J) :
    (inner ℂ x (TF Phi sigma F x)).re ≤ ‖x‖ ^ 2 := by
  simp only [TF, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, inner_sub_right,
    inner_sum, Complex.sub_re, Complex.re_sum]
  have h1 : 0 ≤ ∑ i ∈ F, (inner ℂ x (Bi Phi sigma i x)).re :=
    Finset.sum_nonneg (fun i _ => (Complex.nonneg_iff.mp (bi_pos Phi sigma i x)).1)
  have h2 : (inner ℂ x (coefficientSupportProjection (Phi.val sigma.coefficients) x)).re ≤ ‖x‖ ^ 2 := by
    refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ x) (norm_nonneg _)
  linarith

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

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- U4 core: the diagonal supported duals sum (weakly) to the support projection. -/
lemma bsum {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I) (x : Hilbert J) :
    HasSum (fun i => inner ℂ x (Bi Phi sigma i x))
      (inner ℂ x (coefficientSupportProjection (Phi.val sigma.coefficients) x)) := by
  set rho : State J := ⟨Phi.val sigma.coefficients,
    chan_density Phi.val Phi.property _ sigma.density⟩ with hrho
  have htt : positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) *
      positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)) =
      boundedOperator (Phi.val sigma.coefficients) := (sqrt_state rho).2.1
  set S := coefficientSupportProjection (Phi.val sigma.coefficients) with hS
  set P := boundedOperator (Phi.val sigma.coefficients) with hP
  set t := positiveSquareRoot P with ht
  set v : I → Hilbert I := fun i => positiveSquareRoot (boundedOperator sigma.coefficients) (bvec i)
    with hv
  have hvs : Summable (fun i => ‖v i‖ ^ 2) := (sqrt_state sigma).2.2.summable
  have hpos : ∀ F z, 0 ≤ (inner ℂ z (TF Phi sigma F z)).re :=
    fun F z => (Complex.nonneg_iff.mp (TF_pos Phi sigma F z)).1
  have him : ∀ F z, (inner ℂ z (TF Phi sigma F z)).im = 0 :=
    fun F z => (Complex.nonneg_iff.mp (TF_pos Phi sigma F z)).2.symm
  have key : Tendsto (fun F : Finset I => inner ℂ x (TF Phi sigma F x)) atTop (𝓝 0) := by
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
    have htl : Tendsto (fun F : Finset I => (∑' i, ‖v i‖ ^ 2 - ∑ i ∈ F, ‖v i‖ ^ 2) * ‖y‖ ^ 2)
        atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := ∑' i, ‖v i‖ ^ 2)).sub hvs.hasSum).mul_const (‖y‖ ^ 2)
      simpa using this
    obtain ⟨F0, hF0⟩ := Filter.eventually_atTop.mp
      (htl.eventually (gt_mem_nhds (show (0:ℝ) < ε / 8 by positivity)))
    refine ⟨F0, fun F hF => ?_⟩
    have hty : (inner ℂ (t y) (TF Phi sigma F (t y))).re < ε / 8 := by
      rw [TF_t]
      exact (tail_le Phi sigma.coefficients v hvs (fun p q => dens_exp sigma p q) F y).2.2.trans_lt
        (hF0 F hF)
    have hpb := par_bound (TF Phi sigma F) (hpos F) (TF_le Phi sigma F) (S x) (t y)
    rw [dist_zero_right, TF_S]
    have hre : ‖inner ℂ (S x) (TF Phi sigma F (S x))‖ = (inner ℂ (S x) (TF Phi sigma F (S x))).re := by
      have : inner ℂ (S x) (TF Phi sigma F (S x)) =
          ((inner ℂ (S x) (TF Phi sigma F (S x))).re : ℂ) :=
        Complex.ext (by simp) (by simp [him])
      conv_lhs => rw [this]
      rw [Complex.norm_real, Real.norm_of_nonneg (hpos F _)]
    rw [hre]
    linarith
  have hsum : (fun F : Finset I => ∑ i ∈ F, inner ℂ x (Bi Phi sigma i x)) =
      fun F => inner ℂ x (S x) - inner ℂ x (TF Phi sigma F x) := by
    funext F
    simp only [TF, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, inner_sub_right,
      inner_sum]
    rw [← hS, sub_sub_cancel]
  have hm : Tendsto (fun F : Finset I => ∑ i ∈ F, inner ℂ x (Bi Phi sigma i x)) atTop
      (𝓝 (inner ℂ x (S x))) := by
    rw [hsum]
    simpa using (tendsto_const_nhds (x := inner ℂ x (S x))).sub key
  exact hm

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- U4: normality of the extended Petz dual: its diagonal values sum weakly to the identity. -/
lemma dnorm {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I) (x : Hilbert J) :
    HasSum (fun i => inner ℂ x (petzExtendedDual Phi.val sigma.coefficients (rk (bvec i) (bvec i)) x))
      (inner ℂ x x) := by
  have h1 := bsum Phi sigma x
  have hc : HasSum (fun i => boundedTracePair sigma.coefficients (rk (bvec i) (bvec i))) 1 := by
    have h := (sqrt_state sigma).2.2
    have h' := (Complex.hasSum_ofReal).mpr h
    refine h'.congr_fun (fun i => ?_)
    rw [sig_pair, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h2 := hc.mul_right (inner ℂ x ((ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection (Phi.val sigma.coefficients)) x))
  have h3 := h1.add h2
  have e : inner ℂ x (coefficientSupportProjection (Phi.val sigma.coefficients) x) + 1 * inner ℂ x ((ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection (Phi.val sigma.coefficients)) x) =
      inner ℂ x x := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_sub_right, one_mul]
    ring
  rw [e] at h3
  refine h3.congr_fun (fun i => ?_)
  simp only [petzExtendedDual, Bi, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right]

open scoped ComplexOrder in
lemma d_pos {I J : Type} (Phi : Channel I J) (sigma : State I) (i : I) (y : Hilbert J) :
    0 ≤ inner ℂ y (petzExtendedDual Phi.val sigma.coefficients (rk (bvec i) (bvec i)) y) := by
  have h := u3b Phi sigma (Finset.univ : Finset Unit) (fun _ => bvec i) (fun _ => y)
  simpa using h

lemma slice_sq {J A : Type} (x : Hilbert (J × A)) :
    HasSum (fun a => ‖slice x a‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (Equiv.prodComm A J).hasSum_iff.mpr (hasSum_normSq x)
  exact h.prod_fiberwise (fun a => hasSum_normSq (slice x a))

lemma joint2 {α β : Type} (g : α × β → ℝ) (hg : ∀ p, 0 ≤ g p) {b : β → ℝ} {s : ℝ}
    (hb : ∀ y, HasSum (fun x => g (x, y)) (b y)) (hs : HasSum b s) : HasSum g s := by
  have h := joint1 (g ∘ Prod.swap) (fun p => hg _) (a := b) hb hs
  exact (Equiv.prodComm α β).hasSum_iff.mpr h

open scoped ComplexOrder in
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot) in
/-- U4: the diagonal of every amplification of the Petz recovery map sums to one. -/
lemma theta_diag {I J A : Type} [Countable I] (Phi : Channel I J) (sigma : State I)
    (rho : State (J × A)) :
    HasSum (fun P : I × A =>
      (tensorApply (petzRecovery Phi.val sigma.coefficients) rho.coefficients P P).re) 1 := by
  set D := petzExtendedDual Phi.val sigma.coefficients with hD
  set r := positiveSquareRoot (boundedOperator rho.coefficients) with hr
  set M := tensorApply (petzRecovery Phi.val sigma.coefficients) rho.coefficients with hM
  have hent : ∀ P : I × A, HasSum (fun k => inner ℂ (slice (r (bvec k)) P.2)
      (D (rk (bvec P.1) (bvec P.1)) (slice (r (bvec k)) P.2))) (M P P) := by
    intro P
    have := block_pair rho P.2 P.2 (D (rk (bvec P.1) (bvec P.1)))
    simpa only [hM, tensorApply, petzRecovery, unit_rk] using this
  let g : (J × A) × (I × A) → ℝ := fun q => (inner ℂ (slice (r (bvec q.1)) q.2.2)
    (D (rk (bvec q.2.1) (bvec q.2.1)) (slice (r (bvec q.1)) q.2.2))).re
  have hg : ∀ q, 0 ≤ g q := fun q => (Complex.nonneg_iff.mp (d_pos Phi sigma q.2.1 _)).1
  refine dsum_swap g hg (a := fun k => ‖r (bvec k)‖ ^ 2) (fun k => ?_) (sqrt_state rho).2.2
    (fun P => ?_)
  · refine joint2 (fun P : I × A => g (k, P)) (fun P => hg _)
      (b := fun a => ‖slice (r (bvec k)) a‖ ^ 2) (fun a => ?_) (slice_sq _)
    have h := Complex.reCLM.hasSum (dnorm Phi sigma (slice (r (bvec k)) a))
    have e : (inner ℂ (slice (r (bvec k)) a) (slice (r (bvec k)) a)).re =
        ‖slice (r (bvec k)) a‖ ^ 2 := by
      first
        | exact inner_self_eq_norm_sq (𝕜 := ℂ) _
        | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
        | simp
    simp only [Complex.reCLM_apply, e] at h
    exact h
  · have h := Complex.reCLM.hasSum (hent P)
    simp only [Complex.reCLM_apply] at h
    exact h

theorem theta_cl4 {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I) (n : ℕ)
    (rho : State (J × Fin n)) :
    IsDensity (tensorApply (petzRecovery Phi.val sigma.coefficients) rho.coefficients) := by
  have hd := theta_diag Phi sigma rho
  have hf := theta_forms Phi sigma rho
  exact ⟨(psd_tc hf hd.summable).1, hf, hd.summable, hd.tsum_eq⟩

lemma dens_of_cl4 {I J : Type} (Psi : Matrix I I ℂ → Matrix J J ℂ)
    (h4 : ∀ (n : ℕ) (rho : State (I × Fin n)), IsDensity (tensorApply Psi rho.coefficients))
    (X : Matrix I I ℂ) (hX : IsDensity X) : IsDensity (Psi X) := by
  let e : I × Fin 1 ≃ I := Equiv.prodUnique I (Fin 1)
  have hX1 : IsDensity (X.submatrix e e) := isDensity_reindex e hX
  have hY := h4 1 ⟨X.submatrix e e, hX1⟩
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

lemma theta_zero {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (sigma : Matrix I I ℂ) :
    petzRecovery Phi sigma 0 = 0 := by
  funext i j
  simp only [petzRecovery, boundedTracePair, bO_zero, ContinuousLinearMap.comp_zero]
  simp [operatorCoeff]

lemma theta_mat {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I)
    (w : ℕ → Hilbert J) (hw : Summable (fun n => ‖w n‖ ^ 2)) :
    IsTraceClass (petzRecovery Phi.val sigma.coefficients (Mat w)) := by
  by_cases h0 : (∑' n, ‖w n‖ ^ 2) = 0
  · have hf := (hasSum_zero_iff_of_nonneg (fun n => sq_nonneg ‖w n‖)).mp (h0 ▸ hw.hasSum)
    have hw0 : ∀ n, w n = 0 := fun n => by
      have := congrFun hf n
      simpa using this
    have hM : Mat w = 0 := by funext i j; simp [Mat, hw0]
    rw [hM, theta_zero]
    exact tc_zero
  · have hd := dens_of_cl4 _ (fun n rho => theta_cl4 Phi sigma n rho) _ (isDensity_mat w hw h0)
    have e : Mat w = (((∑' n, ‖w n‖ ^ 2 : ℝ)) : ℂ) •
        ((((∑' n, ‖w n‖ ^ 2)⁻¹ : ℝ) : ℂ) • Mat w) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one, one_smul]
    rw [e, theta_smul _ _ _ (tc_smul _ (tc_mat w hw))]
    exact tc_smul _ hd.1

theorem theta_cl1 {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I)
    (X : Matrix J J ℂ) (hX : IsTraceClass X) :
    IsTraceClass (petzRecovery Phi.val sigma.coefficients X) := by
  obtain ⟨e0⟩ := hX
  obtain ⟨e, he⟩ := balance e0
  have hbal : ∀ n, ‖e.left n‖ = ‖e.right n‖ := fun n => by
    have h : ‖e.left n‖ ^ 2 = ‖e.right n‖ ^ 2 := (he n).1.trans (he n).2.symm
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  rw [polar_split e hbal]
  have hY : ∀ k, IsTraceClass (Mat (wc e k)) := fun k => tc_mat _ (wc_summable e hbal k)
  have key : ∀ m, IsTraceClass (petzRecovery Phi.val sigma.coefficients
      (∑ c ∈ Finset.range m, (Complex.I ^ c / 4) • Mat (wc e c))) := by
    intro m
    induction m with
    | zero => rw [Finset.sum_range_zero, theta_zero]; exact tc_zero
    | succ m ih =>
      rw [Finset.sum_range_succ, theta_add _ _ (tc_sum m _ _ hY) (tc_smul _ (hY m)),
        theta_smul _ _ _ (hY m)]
      exact tc_add ih (tc_smul _ (theta_mat Phi sigma _ (wc_summable e hbal m)))
  exact key 4

/-- C1: the Petz recovery map is a trace-class channel and recovers sigma. -/
theorem c1_full {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I) :
    IsTraceClassChannel (petzRecovery Phi.val sigma.coefficients) ∧
    petzRecovery Phi.val sigma.coefficients (Phi.val sigma.coefficients) = sigma.coefficients :=
  ⟨⟨fun X hX => theta_cl1 Phi sigma X hX, fun _ _ hX hY => theta_add _ _ hX hY,
    fun c _ hX => theta_smul _ _ c hX, fun n rho => theta_cl4 Phi sigma n rho⟩,
    c1_recover Phi sigma⟩

end P45Petz

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

theorem solution
    {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I) :
    IsTraceClassChannel (petzRecovery Phi.val sigma.coefficients) ∧
    petzRecovery Phi.val sigma.coefficients (Phi.val sigma.coefficients) = sigma.coefficients := by
  exact P45Petz.c1_full Phi sigma

end

end ChildRoot
