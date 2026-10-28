-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.extendedRelativeEntropy_monotone_of_finite_ssa
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T00:53:32.397934+00:00
-- url     : https://prove2.me/submissions/e1262428-2ee9-4159-a7b7-2d7aedef6caa

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
import Definitions.Def_SimpleSSA_Monotone_Basic

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
lemma hasSum_basis {I : Type} (x : Hilbert I) :
    HasSum (fun j => x j • (lp.single 2 j (1 : ℂ) : Hilbert I)) x := by
  have h := lp.hasSum_single (E := fun _ : I => ℂ) (p := 2) (by simp) x
  have e : (fun j => x j • (lp.single 2 j (1 : ℂ) : Hilbert I)) = fun j => lp.single 2 j (x j) := by
    funext j; rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [e]; exact h

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


/-! ## Part C: Cauchy-Schwarz on coordinates and the trace formula -/
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

/-! ## B1: a density is a countable sum of rank-one positives (via the CFC square root) -/

/-! ## L4: the square root of a state is self-adjoint Hilbert-Schmidt with HS norm 1 -/

/-! ## s3: Douglas factorization and positivity of channel outputs -/
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

lemma amp_mem {I : Type} {n : ℕ} (x : Fin n → Hilbert I) :
    Memℓp (fun p : I × Fin n => x p.2 p.1) 2 :=
  (memℓp_two_iff' _).mpr (hasSum_prod_fin (f := fun p : I × Fin n => ‖x p.2 p.1‖ ^ 2)
    (fun a => hasSum_normSq (x a))).summable

def amp {I : Type} {n : ℕ} (x : Fin n → Hilbert I) : Hilbert (I × Fin n) :=
  ⟨fun p => x p.2 p.1, amp_mem x⟩

lemma amp_normSq {I : Type} {n : ℕ} (x : Fin n → Hilbert I) :
    ‖amp x‖ ^ 2 = ∑ a, ‖x a‖ ^ 2 :=
  (hasSum_normSq (amp x)).unique (hasSum_prod_fin (f := fun p : I × Fin n => ‖x p.2 p.1‖ ^ 2)
    (fun a => hasSum_normSq (x a)))

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

/-! ## s5: pairing through a rank-one expansion over any index (U3e core) -/

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

section C3aPart

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators ENNReal ComplexOrder Topology Matrix

namespace P45Lsc

open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy)

variable {F : Type} [Fintype F] [DecidableEq F]

/-- Coefficients of `A` in the eigenbasis of `B`. -/
def W (A B : Matrix F F ℂ) (hB : B.IsHermitian) : Matrix F F ℂ :=
  star (hB.eigenvectorUnitary : Matrix F F ℂ) * A * (hB.eigenvectorUnitary : Matrix F F ℂ)

lemma tr_mul_cfc (A B : Matrix F F ℂ) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f B).trace = ∑ k, W A B hB k k * (f (hB.eigenvalues k) : ℂ) := by
  rw [hB.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [show A * ((hB.eigenvectorUnitary : Matrix F F ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ f ∘ hB.eigenvalues) * star (hB.eigenvectorUnitary : Matrix F F ℂ))
      = (A * (hB.eigenvectorUnitary : Matrix F F ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ f ∘ hB.eigenvalues)) * star (hB.eigenvectorUnitary : Matrix F F ℂ)
      by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, W, Function.comp_apply]
  rfl

lemma re_tr_mul_cfc (A B : Matrix F F ℂ) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f B).trace.re = ∑ k, (W A B hB k k).re * f (hB.eigenvalues k) := by
  rw [tr_mul_cfc A B hB f, Complex.re_sum]
  simp [Complex.mul_re]

lemma W_diag_nonneg (A B : Matrix F F ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian) (k : F) :
    0 ≤ W A B hB k k := by
  have h := hA.conjTranspose_mul_mul_same (hB.eigenvectorUnitary : Matrix F F ℂ)
  have := h.diag_nonneg (i := k)
  simpa [W, Matrix.star_eq_conjTranspose] using this

lemma W_re_nonneg (A B : Matrix F F ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian) (k : F) :
    0 ≤ (W A B hB k k).re :=
  (Complex.nonneg_iff.mp (W_diag_nonneg A B hA hB k)).1

lemma W_eq_re (A B : Matrix F F ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian) (k : F) :
    W A B hB k k = ((W A B hB k k).re : ℂ) := by
  have h := Complex.nonneg_iff.mp (W_diag_nonneg A B hA hB k)
  apply Complex.ext <;> simp [h.2]

lemma W_as_dot (A B : Matrix F F ℂ) (hB : B.IsHermitian) (k : F) :
    W A B hB k k = star (fun j => (hB.eigenvectorUnitary : Matrix F F ℂ) j k) ⬝ᵥ
      (A *ᵥ fun j => (hB.eigenvectorUnitary : Matrix F F ℂ) j k) := by
  simp only [W, Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum, Matrix.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma Ustar_B_U (B : Matrix F F ℂ) (hB : B.IsHermitian) :
    star (hB.eigenvectorUnitary : Matrix F F ℂ) * B * (hB.eigenvectorUnitary : Matrix F F ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
  have := hB.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa using this

lemma U_mul_star (B : Matrix F F ℂ) (hB : B.IsHermitian) :
    (hB.eigenvectorUnitary : Matrix F F ℂ) * star (hB.eigenvectorUnitary : Matrix F F ℂ) = 1 :=
  Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2

lemma B_mul_U (B : Matrix F F ℂ) (hB : B.IsHermitian) :
    B * (hB.eigenvectorUnitary : Matrix F F ℂ) =
      (hB.eigenvectorUnitary : Matrix F F ℂ) * Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
  rw [← Ustar_B_U B hB]
  calc B * (hB.eigenvectorUnitary : Matrix F F ℂ)
      = ((hB.eigenvectorUnitary : Matrix F F ℂ) * star (hB.eigenvectorUnitary : Matrix F F ℂ)) * B *
          (hB.eigenvectorUnitary : Matrix F F ℂ) := by rw [U_mul_star, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma ker_iff (A B : Matrix F F ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin ↔
      ∀ k, hB.eigenvalues k = 0 → W A B hB k k = 0 := by
  set U : Matrix F F ℂ := (hB.eigenvectorUnitary : Matrix F F ℂ) with hU
  constructor
  · intro h k hk
    have hv : B *ᵥ (fun j => U j k) = 0 := by
      funext j
      have := congrFun (congrFun (B_mul_U B hB) j) k
      rw [Matrix.mul_diagonal] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hU, hk] using this
    have hAv : A *ᵥ (fun j => U j k) = 0 := by
      have := h (show (fun j => U j k) ∈ LinearMap.ker B.mulVecLin by simpa using hv)
      simpa using this
    rw [W_as_dot, ← hU, hAv, dotProduct_zero]
  · intro h x hx
    have hx' : B *ᵥ x = 0 := by simpa using hx
    set w := star U *ᵥ x with hw
    have hxw : x = U *ᵥ w := by
      rw [hw, Matrix.mulVec_mulVec, hU, U_mul_star, Matrix.one_mulVec]
    have hbw : ∀ k, hB.eigenvalues k ≠ 0 → w k = 0 := by
      intro k hk
      have h0 : (star U * B * U) *ᵥ w = 0 := by
        rw [← Matrix.mulVec_mulVec, ← hxw, ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_zero]
      rw [hU, Ustar_B_U] at h0
      have := congrFun h0 k
      rw [Matrix.mulVec_diagonal] at this
      simp only [Function.comp_apply, Pi.zero_apply, mul_eq_zero] at this
      rcases this with h1 | h1
      · exact absurd (by simpa using h1) hk
      · exact h1
    have hAk : ∀ k, hB.eigenvalues k = 0 → A *ᵥ (fun j => U j k) = 0 := by
      intro k hk
      rw [← Matrix.PosSemidef.dotProduct_mulVec_zero_iff hA]
      rw [← W_as_dot]
      exact h k hk
    show A *ᵥ x = 0
    rw [hxw, Matrix.mulVec_mulVec]
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : hB.eigenvalues k = 0
    · have := congrFun (hAk k hk) i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [Matrix.mul_apply, this, zero_mul]
    · rw [hbw k hk, mul_zero]

/-- The `ε`-regularised Lindblad expression. -/
def gε (A B : Matrix F F ℂ) (ε : ℝ) : ℝ :=
  (A * cfc Real.log A).trace.re - (A * cfc (fun x => Real.log (x + ε)) B).trace.re +
    B.trace.re - A.trace.re

lemma fre_val (A B : Matrix F F ℂ) :
    (A * cfc Real.log A - A * cfc Real.log B + B - A).trace.re =
      (A * cfc Real.log A).trace.re - (A * cfc Real.log B).trace.re + B.trace.re - A.trace.re := by
  simp only [Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]

/-- Lindblad's finite relative entropy is the increasing limit of its `ε`-regularisations. -/
theorem fre_iSup (A B : Matrix F F ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    finiteRelativeEntropy A B = ⨆ n : ℕ, ENNReal.ofReal (gε A B (1 / ((n:ℝ) + 1))) := by
  have hH := hB.isHermitian
  have hg : ∀ ε, gε A B ε = ((A * cfc Real.log A).trace.re + B.trace.re - A.trace.re) -
      ∑ k, (W A B hH k k).re * Real.log (hH.eigenvalues k + ε) := by
    intro ε; rw [gε, re_tr_mul_cfc A B hH]; ring
  have hc0 : ∀ k, 0 ≤ (W A B hH k k).re := fun k => W_re_nonneg A B hA hH k
  have hb0 : ∀ k, 0 ≤ hH.eigenvalues k := fun k => hB.eigenvalues_nonneg k
  have hεpos : ∀ n : ℕ, 0 < 1 / ((n:ℝ) + 1) := fun n => by positivity
  have hmono : Monotone (fun n : ℕ => ENNReal.ofReal (gε A B (1 / ((n:ℝ) + 1)))) := by
    refine monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal ?_
    rw [hg, hg]
    have : ∑ k, (W A B hH k k).re * Real.log (hH.eigenvalues k + 1 / (((n+1:ℕ):ℝ) + 1)) ≤
        ∑ k, (W A B hH k k).re * Real.log (hH.eigenvalues k + 1 / ((n:ℝ) + 1)) := by
      refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hc0 k)
      have h1 : 1 / (((n+1:ℕ):ℝ) + 1) ≤ 1 / ((n:ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity); push_cast; linarith
      exact Real.log_le_log (by have := hεpos (n+1); linarith [hb0 k]) (by linarith)
    linarith
  have hε0 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold finiteRelativeEntropy
  split_ifs with hker
  · have hz := (ker_iff A B hA hH).mp hker
    have hcz : ∀ k, hH.eigenvalues k = 0 → (W A B hH k k).re = 0 := fun k hk => by simp [hz k hk]
    have hval : (A * cfc Real.log A - A * cfc Real.log B + B - A).trace.re =
        ((A * cfc Real.log A).trace.re + B.trace.re - A.trace.re) -
          ∑ k, (W A B hH k k).re * Real.log (hH.eigenvalues k) := by
      rw [fre_val, re_tr_mul_cfc A B hH]; ring
    have hlim : Tendsto (fun n : ℕ => gε A B (1 / ((n:ℝ) + 1))) atTop
        (𝓝 (((A * cfc Real.log A).trace.re + B.trace.re - A.trace.re) -
          ∑ k, (W A B hH k k).re * Real.log (hH.eigenvalues k))) := by
      simp_rw [hg]
      refine tendsto_const_nhds.sub (tendsto_finsetSum _ fun k _ => ?_)
      by_cases hk : hH.eigenvalues k = 0
      · simp [hcz k hk]
      · refine Tendsto.const_mul _ ?_
        have hpos : 0 < hH.eigenvalues k := lt_of_le_of_ne (hb0 k) (Ne.symm hk)
        have h2 : Tendsto (fun n : ℕ => hH.eigenvalues k + 1 / ((n:ℝ) + 1)) atTop
            (𝓝 (hH.eigenvalues k)) := by
          simpa using (tendsto_const_nhds (x := hH.eigenvalues k)).add hε0
        exact ((Real.continuousAt_log hpos.ne').tendsto).comp h2
    rw [hval]
    exact (tendsto_nhds_unique (tendsto_atTop_iSup hmono) (ENNReal.tendsto_ofReal hlim)).symm
  · have hz : ¬ ∀ k, hH.eigenvalues k = 0 → W A B hH k k = 0 :=
      fun h => hker ((ker_iff A B hA hH).mpr h)
    push_neg at hz
    obtain ⟨k0, hk0, hW⟩ := hz
    have hc0pos : 0 < (W A B hH k0 k0).re := by
      rcases (hc0 k0).lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [W_eq_re A B hA hH k0, ← h]; simp) hW
    symm
    rw [iSup_eq_top]
    intro r hr
    have hlow : ∀ n : ℕ, ((A * cfc Real.log A).trace.re + B.trace.re - A.trace.re) -
        (∑ k ∈ Finset.univ.erase k0, (W A B hH k k).re * Real.log (hH.eigenvalues k + 1)) +
        (W A B hH k0 k0).re * Real.log ((n:ℝ) + 1) ≤ gε A B (1 / ((n:ℝ) + 1)) := by
      intro n
      rw [hg, ← Finset.add_sum_erase _ _ (Finset.mem_univ k0), hk0, zero_add, one_div, Real.log_inv]
      have : ∑ k ∈ Finset.univ.erase k0, (W A B hH k k).re * Real.log (hH.eigenvalues k + ((n:ℝ) + 1)⁻¹)
          ≤ ∑ k ∈ Finset.univ.erase k0, (W A B hH k k).re * Real.log (hH.eigenvalues k + 1) := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hc0 k)
        have h1 : ((n:ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
        have h2 : 0 < ((n:ℝ) + 1)⁻¹ := by positivity
        exact Real.log_le_log (by linarith [hb0 k]) (by linarith)
      linarith
    have htend : Tendsto (fun n : ℕ => ((A * cfc Real.log A).trace.re + B.trace.re - A.trace.re) -
        (∑ k ∈ Finset.univ.erase k0, (W A B hH k k).re * Real.log (hH.eigenvalues k + 1)) +
        (W A B hH k0 k0).re * Real.log ((n:ℝ) + 1)) atTop atTop := by
      refine tendsto_atTop_add_const_left _ _ (Tendsto.const_mul_atTop hc0pos ?_)
      exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop r.toReal).exists
    refine ⟨n, ?_⟩
    calc r = ENNReal.ofReal r.toReal := (ENNReal.ofReal_toReal hr.ne).symm
      _ < ENNReal.ofReal (gε A B (1 / ((n:ℝ) + 1))) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr (by linarith [hlow n])

/-! ## Continuity of the regularised expression and lower semicontinuity -/

lemma spec_nonneg (M : Matrix F F ℂ) (hM : M.PosSemidef) : spectrum ℝ M ⊆ Set.Ici 0 := by
  intro x hx
  rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨k, rfl⟩ := hx
  exact hM.eigenvalues_nonneg k

open scoped Matrix.Norms.L2Operator in
lemma cfc_contOn_psd (f : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s) (hsub : Set.Ici (0:ℝ) ⊆ s)
    (hf : ContinuousOn f s) :
    ContinuousOn (fun M : Matrix F F ℂ => cfc f M) {M | M.PosSemidef} := by
  refine ContinuousOn.cfc_of_mem_nhdsSet (𝕜 := ℝ) (s := s) f (a := fun M => M) ?_ continuousOn_id
    (fun M hM => hM.isHermitian.isSelfAdjoint) hf
  refine hs.mem_nhdsSet.mpr (Set.iUnion₂_subset fun M hM => (spec_nonneg M hM).trans hsub)

lemma tendsto_cfc_psd (f : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s) (hsub : Set.Ici (0:ℝ) ⊆ s)
    (hf : ContinuousOn f s) {a : ℕ → Matrix F F ℂ} {A : Matrix F F ℂ}
    (ha : ∀ n, (a n).PosSemidef) (hA : A.PosSemidef) (h : Tendsto a atTop (𝓝 A)) :
    Tendsto (fun n => cfc f (a n)) atTop (𝓝 (cfc f A)) := by
  have hc := (cfc_contOn_psd (F := F) f s hs hsub hf) A hA
  exact hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨h, Eventually.of_forall ha⟩)

lemma mul_cfc_log (A : Matrix F F ℂ) (hA : A.IsHermitian) :
    A * cfc Real.log A = cfc (fun x => x * Real.log x) A := by
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  rw [cfc_mul (fun x => x) Real.log A (hfin.continuousOn _) (hfin.continuousOn _),
    cfc_id' ℝ A hA.isSelfAdjoint]

lemma tr_re_tendsto {M : ℕ → Matrix F F ℂ} {M0 : Matrix F F ℂ} (h : Tendsto M atTop (𝓝 M0)) :
    Tendsto (fun n => (M n).trace.re) atTop (𝓝 M0.trace.re) :=
  ((Complex.continuous_re.comp (continuous_id.matrix_trace)).tendsto M0).comp h

lemma gε_tendsto (ε : ℝ) (hε : 0 < ε) {a b : ℕ → Matrix F F ℂ} {A B : Matrix F F ℂ}
    (ha : ∀ n, (a n).PosSemidef) (hb : ∀ n, (b n).PosSemidef) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hta : Tendsto a atTop (𝓝 A)) (htb : Tendsto b atTop (𝓝 B)) :
    Tendsto (fun n => gε (a n) (b n) ε) atTop (𝓝 (gε A B ε)) := by
  have h1 : Tendsto (fun n => cfc (fun x => x * Real.log x) (a n)) atTop
      (𝓝 (cfc (fun x => x * Real.log x) A)) :=
    tendsto_cfc_psd _ Set.univ isOpen_univ (Set.subset_univ _)
      (Real.continuous_mul_log.continuousOn) ha hA hta
  have h2 : Tendsto (fun n => cfc (fun x => Real.log (x + ε)) (b n)) atTop
      (𝓝 (cfc (fun x => Real.log (x + ε)) B)) := by
    refine tendsto_cfc_psd _ (Set.Ioi (-ε)) isOpen_Ioi
      (fun x hx => by simp only [Set.mem_Ici] at hx; simp only [Set.mem_Ioi]; linarith) ?_ hb hB htb
    refine ContinuousOn.log (by fun_prop) fun x hx => ?_
    simp only [Set.mem_Ioi] at hx; linarith
  have h3 := tr_re_tendsto (hta.mul h2)
  have h4 := tr_re_tendsto h1
  have h5 := tr_re_tendsto hta
  have h6 := tr_re_tendsto htb
  have e : ∀ n, gε (a n) (b n) ε = (cfc (fun x => x * Real.log x) (a n)).trace.re -
      (a n * cfc (fun x => Real.log (x + ε)) (b n)).trace.re + (b n).trace.re - (a n).trace.re :=
    fun n => by rw [gε, mul_cfc_log _ (ha n).isHermitian]
  rw [show gε A B ε = (cfc (fun x => x * Real.log x) A).trace.re -
      (A * cfc (fun x => Real.log (x + ε)) B).trace.re + B.trace.re - A.trace.re by
    rw [gε, mul_cfc_log _ hA.isHermitian]]
  simp_rw [e]
  exact ((h4.sub h3).add h6).sub h5

/-- Lower semicontinuity of Lindblad's finite relative entropy on positive matrices. -/
theorem fre_lsc {a b : ℕ → Matrix F F ℂ} {A B : Matrix F F ℂ}
    (ha : ∀ n, (a n).PosSemidef) (hb : ∀ n, (b n).PosSemidef) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hta : Tendsto a atTop (𝓝 A)) (htb : Tendsto b atTop (𝓝 B)) :
    finiteRelativeEntropy A B ≤ liminf (fun n => finiteRelativeEntropy (a n) (b n)) atTop := by
  rw [fre_iSup A B hA hB]
  refine iSup_le fun m => ?_
  have hε : (0:ℝ) < 1 / ((m:ℝ) + 1) := by positivity
  have ht := ENNReal.tendsto_ofReal (gε_tendsto _ hε ha hb hA hB hta htb)
  rw [← ht.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  rw [fre_iSup _ _ (ha n) (hb n)]
  exact le_iSup (fun m : ℕ => ENNReal.ofReal (gε (a n) (b n) (1 / ((m:ℝ) + 1)))) m

/-! ## Unitary invariance (C3a ingredient) -/

section Unitary
variable (u : Matrix F F ℂ) (hu : u ∈ unitary (Matrix F F ℂ))
include hu

lemma mul_conj (X Y : Matrix F F ℂ) :
    (u * X * star u) * (u * Y * star u) = u * (X * Y) * star u := by
  calc (u * X * star u) * (u * Y * star u) = u * X * (star u * u) * Y * star u := by
        simp only [Matrix.mul_assoc]
    _ = u * (X * Y) * star u := by
        rw [Unitary.star_mul_self_of_mem hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]

end Unitary

end P45Lsc

namespace P45Dpi

open P45Lsc

open QAlgorithms.Papers.Independent.Frontier18.P07 (finiteRelativeEntropy)

/-! ## Functional calculus of block / isometric embeddings (f 0 = 0) -/

lemma exists_poly (s : Finset ℝ) (f : ℝ → ℝ) : ∃ p : Polynomial ℝ, ∀ x ∈ s, p.eval x = f x := by
  refine ⟨Lagrange.interpolate s id f, fun x hx => ?_⟩
  have := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _) hx
  simpa using this

lemma aeval_succ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (p : Polynomial ℝ)
    (h0 : p.coeff 0 = 0) :
    Polynomial.aeval M p = ∑ i ∈ Finset.range p.natDegree, p.coeff (i+1) • M ^ (i+1) := by
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self p.natDegree), Finset.sum_range_succ', h0,
    zero_smul, add_zero]

lemma cfc_eq_aeval {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (p : Polynomial ℝ) (f : ℝ → ℝ) (hs : ∀ x ∈ spectrum ℝ A, p.eval x = f x) :
    cfc f A = Polynomial.aeval A p := by
  rw [← cfc_polynomial p A hA.isSelfAdjoint]
  exact cfc_congr (fun x hx => (hs x hx).symm)

variable {S1 S2 T : Type} [Fintype S1] [DecidableEq S1] [Fintype S2] [DecidableEq S2]
  [Fintype T] [DecidableEq T]

lemma cfc_blocks (M : Matrix T T ℂ) (A1 : Matrix S1 S1 ℂ) (A2 : Matrix S2 S2 ℂ)
    (V1 : Matrix T S1 ℂ) (V2 : Matrix T S2 ℂ)
    (hM : M.IsHermitian) (h1 : A1.IsHermitian) (h2 : A2.IsHermitian)
    (hpow : ∀ n : ℕ, M ^ (n+1) = V1 * A1 ^ (n+1) * V1ᴴ + V2 * A2 ^ (n+1) * V2ᴴ)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    cfc f M = V1 * cfc f A1 * V1ᴴ + V2 * cfc f A2 * V2ᴴ := by
  have fM : (spectrum ℝ M).Finite := Matrix.finite_real_spectrum
  have f1 : (spectrum ℝ A1).Finite := Matrix.finite_real_spectrum
  have f2 : (spectrum ℝ A2).Finite := Matrix.finite_real_spectrum
  obtain ⟨p, hp⟩ := exists_poly (insert 0 (fM.toFinset ∪ f1.toFinset ∪ f2.toFinset)) f
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (Finset.mem_insert_self _ _), hf]
  rw [cfc_eq_aeval M hM p f (fun x hx => hp x (by simp [hx])),
    cfc_eq_aeval A1 h1 p f (fun x hx => hp x (by simp [hx])),
    cfc_eq_aeval A2 h2 p f (fun x hx => hp x (by simp [hx])),
    aeval_succ _ p h0, aeval_succ _ p h0, aeval_succ _ p h0]
  simp only [hpow, smul_add, Finset.sum_add_distrib, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

lemma pow_blocks (A1 : Matrix S1 S1 ℂ) (A2 : Matrix S2 S2 ℂ)
    (V1 : Matrix T S1 ℂ) (V2 : Matrix T S2 ℂ)
    (e1 : V1ᴴ * V1 * A1 = A1) (e2 : V2ᴴ * V2 * A2 = A2) (e12 : V1ᴴ * V2 = 0) (n : ℕ) :
    (V1 * A1 * V1ᴴ + V2 * A2 * V2ᴴ) ^ (n+1) =
      V1 * A1 ^ (n+1) * V1ᴴ + V2 * A2 ^ (n+1) * V2ᴴ := by
  have e21 : V2ᴴ * V1 = 0 := by
    have := congrArg Matrix.conjTranspose e12
    simpa [Matrix.conjTranspose_mul] using this
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ A1 (n+1), pow_succ A2 (n+1)]
    have k1 : V1 * A1 ^ (n+1) * V1ᴴ * (V1 * A1 * V1ᴴ) = V1 * (A1 ^ (n+1) * A1) * V1ᴴ := by
      calc V1 * A1 ^ (n+1) * V1ᴴ * (V1 * A1 * V1ᴴ) = V1 * A1 ^ (n+1) * (V1ᴴ * V1 * A1) * V1ᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1]; simp only [Matrix.mul_assoc]
    have k2 : V2 * A2 ^ (n+1) * V2ᴴ * (V2 * A2 * V2ᴴ) = V2 * (A2 ^ (n+1) * A2) * V2ᴴ := by
      calc V2 * A2 ^ (n+1) * V2ᴴ * (V2 * A2 * V2ᴴ) = V2 * A2 ^ (n+1) * (V2ᴴ * V2 * A2) * V2ᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [e2]; simp only [Matrix.mul_assoc]
    have k3 : V1 * A1 ^ (n+1) * V1ᴴ * (V2 * A2 * V2ᴴ) = 0 := by
      calc V1 * A1 ^ (n+1) * V1ᴴ * (V2 * A2 * V2ᴴ) = V1 * A1 ^ (n+1) * (V1ᴴ * V2) * A2 * V2ᴴ := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [e12]; simp
    have k4 : V2 * A2 ^ (n+1) * V2ᴴ * (V1 * A1 * V1ᴴ) = 0 := by
      calc V2 * A2 ^ (n+1) * V2ᴴ * (V1 * A1 * V1ᴴ) = V2 * A2 ^ (n+1) * (V2ᴴ * V1) * A1 * V1ᴴ := by
            simp only [Matrix.mul_assoc]
        _ = 0 := by rw [e21]; simp
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, k1, k2, k3, k4]
    abel

/-- Functional calculus commutes with an isometric embedding when `f 0 = 0`. -/
lemma cfc_iso (A : Matrix S1 S1 ℂ) (hA : A.IsHermitian) (V : Matrix T S1 ℂ) (hV : Vᴴ * V = 1)
    (f : ℝ → ℝ) (hf : f 0 = 0) : cfc f (V * A * Vᴴ) = V * cfc f A * Vᴴ := by
  have hM : (V * A * Vᴴ).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V hA
  have h := cfc_blocks (V * A * Vᴴ) A (0 : Matrix S1 S1 ℂ) V (0 : Matrix T S1 ℂ) hM hA
    Matrix.isHermitian_zero (fun n => by
      have := pow_blocks A (0 : Matrix S1 S1 ℂ) V (0 : Matrix T S1 ℂ) (by rw [hV, Matrix.one_mul])
        (by simp) (by simp) n
      simpa using this) f hf
  simpa using h

/-! ## Isometric invariance of Lindblad's finite relative entropy -/

lemma ker_iso (A B : Matrix S1 S1 ℂ) (V : Matrix T S1 ℂ) (hV : Vᴴ * V = 1) :
    LinearMap.ker (V * B * Vᴴ).mulVecLin ≤ LinearMap.ker (V * A * Vᴴ).mulVecLin ↔
      LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  constructor
  · intro h x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    have h1 : (V * B * Vᴴ) *ᵥ (V *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hV, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    have h2 := h (show V *ᵥ x ∈ LinearMap.ker (V * B * Vᴴ).mulVecLin by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h1)
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_assoc, hV, Matrix.mul_one, ← Matrix.mulVec_mulVec] at h2
    have := congrArg (fun z => Vᴴ *ᵥ z) h2
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
    rwa [← Matrix.mul_assoc, hV, Matrix.one_mul] at this
  · intro h y hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy ⊢
    have h1 : B *ᵥ (Vᴴ *ᵥ y) = 0 := by
      have := congrArg (fun z => Vᴴ *ᵥ z) hy
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rw [Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul] at this
      exact this
    have h2 := h (show Vᴴ *ᵥ y ∈ LinearMap.ker B.mulVecLin by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h1)
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]

lemma tr_iso (X : Matrix S1 S1 ℂ) (V : Matrix T S1 ℂ) (hV : Vᴴ * V = 1) :
    (V * X * Vᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

lemma mul_iso (X Y : Matrix S1 S1 ℂ) (V : Matrix T S1 ℂ) (hV : Vᴴ * V = 1) :
    (V * X * Vᴴ) * (V * Y * Vᴴ) = V * (X * Y) * Vᴴ := by
  calc (V * X * Vᴴ) * (V * Y * Vᴴ) = V * X * (Vᴴ * V) * Y * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * (X * Y) * Vᴴ := by rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem fre_iso (A B : Matrix S1 S1 ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (V : Matrix T S1 ℂ) (hV : Vᴴ * V = 1) :
    finiteRelativeEntropy (V * A * Vᴴ) (V * B * Vᴴ) = finiteRelativeEntropy A B := by
  unfold finiteRelativeEntropy
  rw [ker_iso A B V hV, cfc_iso A hA V hV _ Real.log_zero, cfc_iso B hB V hV _ Real.log_zero,
    mul_iso _ _ V hV, mul_iso _ _ V hV]
  have e : ∀ X Y Z W : Matrix S1 S1 ℂ, V * X * Vᴴ - V * Y * Vᴴ + V * Z * Vᴴ - V * W * Vᴴ =
      V * (X - Y + Z - W) * Vᴴ := by
    intro X Y Z W; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul]
  rw [e, tr_iso _ V hV]


/-! ## Shift continuity: D_L(X + δ, Y + δ) → D_L(X, Y) as δ → 0 -/

section Shift
variable {F : Type} [Fintype F] [DecidableEq F]

lemma cfc_shift (Y : Matrix F F ℂ) (hY : Y.IsHermitian) (g : ℝ → ℝ) (δ : ℝ) :
    cfc g (Y + δ • (1 : Matrix F F ℂ)) = cfc (fun x => g (x + δ)) Y := by
  have hfin : (spectrum ℝ Y).Finite := Matrix.finite_real_spectrum
  have h1 : cfc (fun x : ℝ => x + δ) Y = Y + δ • (1 : Matrix F F ℂ) := by
    rw [cfc_add_const δ (fun x => x) Y (hfin.continuousOn _) hY.isSelfAdjoint,
      cfc_id' ℝ Y hY.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  rw [← h1, ← cfc_comp' g (fun x => x + δ) Y ((hfin.image _).continuousOn _) (hfin.continuousOn _)
    hY.isSelfAdjoint]

lemma W_shift (X Y : Matrix F F ℂ) (hY : Y.IsHermitian) (δ : ℝ) (k : F) :
    W (X + δ • (1 : Matrix F F ℂ)) Y hY k k = W X Y hY k k + δ := by
  have hu : star (hY.eigenvectorUnitary : Matrix F F ℂ) * (hY.eigenvectorUnitary : Matrix F F ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hu,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  simp

lemma posDef_shift (X : Matrix F F ℂ) (hX : X.PosSemidef) (δ : ℝ) (hδ : 0 < δ) :
    (X + δ • (1 : Matrix F F ℂ)).PosDef := by
  have h1 : (δ • (1 : Matrix F F ℂ)).PosDef := Matrix.PosDef.one.smul hδ
  exact Matrix.PosDef.posSemidef_add hX h1

lemma ker_posDef (A B : Matrix F F ℂ) (hB : B.PosDef) :
    LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
  by_cases h0 : x = 0
  · simp [h0]
  · have := hB.dotProduct_mulVec_pos h0
    rw [hx, dotProduct_zero] at this
    exact absurd this (lt_irrefl 0)

theorem fre_shift_tendsto (X Y : Matrix F F ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hk : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    Tendsto (fun n : ℕ => finiteRelativeEntropy (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ))
      (Y + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ))) atTop (𝓝 (finiteRelativeEntropy X Y)) := by
  have hδ0 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδpos : ∀ n : ℕ, (0:ℝ) < 1 / ((n:ℝ) + 1) := fun n => by positivity
  have heq : ∀ n : ℕ, finiteRelativeEntropy (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ))
      (Y + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) =
      ENNReal.ofReal (((X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) *
        cfc Real.log (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) -
        (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) *
        cfc Real.log (Y + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) +
        (Y + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) -
        (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ))).trace.re) := by
    intro n
    unfold finiteRelativeEntropy
    rw [if_pos (ker_posDef _ _ (posDef_shift Y hY _ (hδpos n)))]
  rw [funext heq]
  unfold finiteRelativeEntropy
  rw [if_pos hk]
  refine ENNReal.tendsto_ofReal ?_
  simp only [fre_val]
  have hXn : Tendsto (fun n : ℕ => X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) atTop (𝓝 X) := by
    have := (tendsto_const_nhds (x := X)).add (hδ0.smul_const (1 : Matrix F F ℂ))
    simpa using this
  have hYn : Tendsto (fun n : ℕ => Y + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) atTop (𝓝 Y) := by
    have := (tendsto_const_nhds (x := Y)).add (hδ0.smul_const (1 : Matrix F F ℂ))
    simpa using this
  have t1 : Tendsto (fun n : ℕ => ((X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) *
      cfc Real.log (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ))).trace.re) atTop
      (𝓝 (X * cfc Real.log X).trace.re) := by
    have e : ∀ n : ℕ, (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) *
        cfc Real.log (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) =
        cfc (fun x => x * Real.log x) (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) :=
      fun n => mul_cfc_log _ (posDef_shift X hX _ (hδpos n)).isHermitian
    simp_rw [e]
    rw [mul_cfc_log X hX.isHermitian]
    exact tr_re_tendsto (tendsto_cfc_psd _ Set.univ isOpen_univ (Set.subset_univ _)
      Real.continuous_mul_log.continuousOn
      (fun n => (posDef_shift X hX _ (hδpos n)).posSemidef) hX hXn)
  have t2 : Tendsto (fun n : ℕ => ((X + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ)) *
      cfc Real.log (Y + (1 / ((n:ℝ) + 1)) • (1 : Matrix F F ℂ))).trace.re) atTop
      (𝓝 (X * cfc Real.log Y).trace.re) := by
    simp_rw [cfc_shift Y hY.isHermitian Real.log, re_tr_mul_cfc _ Y hY.isHermitian, W_shift]
    refine tendsto_finset_sum _ fun k _ => ?_
    by_cases hk0 : hY.isHermitian.eigenvalues k = 0
    · have hW : W X Y hY.isHermitian k k = 0 := (ker_iff X Y hX hY.isHermitian).mp hk k hk0
      rw [hW, hk0]
      simp only [Complex.add_re, Complex.zero_re, Complex.ofReal_re, zero_add, Real.log_zero,
        mul_zero]
      have h2 := (Real.continuous_mul_log.tendsto 0).comp hδ0
      rw [zero_mul] at h2
      exact Tendsto.congr (fun n => by simp) h2
    · refine Tendsto.mul ?_ ?_
      · simp only [Complex.add_re, Complex.ofReal_re]
        simpa using (tendsto_const_nhds (x := (W X Y hY.isHermitian k k).re)).add hδ0
      · refine ((Real.continuousAt_log hk0).tendsto).comp ?_
        simpa using (tendsto_const_nhds (x := hY.isHermitian.eigenvalues k)).add hδ0
  exact ((t1.sub t2).add (tr_re_tendsto hYn)).sub (tr_re_tendsto hXn)

end Shift


/-! ## Partial-trace monotonicity for positive definite pairs, from eq_4 (Proved ca864458) -/

section PTM
open WildeQIT (partialTraceRight)
open SimpleSSA.Monotone (relEntropy)

/-- `SimpleSSA.Monotone.eq_4` (Nielsen-Petz (4), Proved on the platform as ca864458), as a hypothesis. -/
def EQ4 : Prop := ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ρ σ : Matrix (A × B) (A × B) ℂ), QAlgorithms.IsDensityMatrix ρ → ρ.PosDef →
    QAlgorithms.IsDensityMatrix σ → σ.PosDef →
    relEntropy (partialTraceRight ρ) (partialTraceRight σ) ≤ relEntropy ρ σ

variable {F : Type} [Fintype F] [DecidableEq F]

lemma spec_pos (M : Matrix F F ℂ) (hM : M.PosDef) : ∀ x ∈ spectrum ℝ M, 0 < x := by
  intro x hx
  rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨k, rfl⟩ := hx
  exact hM.eigenvalues_pos k

lemma cfc_log_smul (ρ : Matrix F F ℂ) (hρ : ρ.PosDef) (a : ℝ) (ha : 0 < a) :
    cfc Real.log (a • ρ) = Real.log a • (1 : Matrix F F ℂ) + cfc Real.log ρ := by
  have hfin : (spectrum ℝ ρ).Finite := Matrix.finite_real_spectrum
  rw [← cfc_comp_smul a Real.log ρ ((hfin.image _).continuousOn _) hρ.isHermitian.isSelfAdjoint]
  have : cfc (fun x => Real.log (a • x)) ρ = cfc (fun x => Real.log a + Real.log x) ρ := by
    refine cfc_congr fun x hx => ?_
    have hx0 := spec_pos ρ hρ x hx
    simp only [smul_eq_mul]
    rw [Real.log_mul ha.ne' hx0.ne']
  rw [this, cfc_const_add (Real.log a) Real.log ρ (hfin.continuousOn _) hρ.isHermitian.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one]

lemma re_tr_scale (ρ σ : Matrix F F ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    ((a • ρ) * cfc Real.log (a • ρ) - (a • ρ) * cfc Real.log (b • σ) + b • σ - a • ρ).trace.re =
      a * relEntropy ρ σ + (a * Real.log a - a * Real.log b - a) * ρ.trace.re +
        b * σ.trace.re := by
  rw [cfc_log_smul ρ hρ a ha, cfc_log_smul σ hσ b hb]
  simp only [relEntropy, TroppMatrixConcentration.matrixLog, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul]
  ring

lemma trace_ofReal (X : Matrix F F ℂ) (hX : X.IsHermitian) : X.trace = ((X.trace.re : ℝ) : ℂ) := by
  rw [hX.trace_eq_sum_eigenvalues]
  simp

lemma trace_pos [Nonempty F] (X : Matrix F F ℂ) (hX : X.PosDef) : 0 < X.trace.re := by
  rw [hX.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  exact Finset.sum_pos (fun i _ => by simpa using hX.eigenvalues_pos i) Finset.univ_nonempty

variable {T E : Type} [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

lemma ptr_smul (a : ℝ) (X : Matrix (T × E) (T × E) ℂ) :
    partialTraceRight (a • X) = a • partialTraceRight X := by
  ext i j; simp [partialTraceRight, Finset.smul_sum]

lemma ptr_add (X Y : Matrix (T × E) (T × E) ℂ) :
    partialTraceRight (X + Y) = partialTraceRight X + partialTraceRight Y := by
  ext i j; simp [partialTraceRight, Finset.sum_add_distrib]

lemma ptr_trace (X : Matrix (T × E) (T × E) ℂ) : (partialTraceRight X).trace = X.trace := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

lemma ptr_herm (X : Matrix (T × E) (T × E) ℂ) (hX : X.IsHermitian) :
    (partialTraceRight X).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, partialTraceRight, Matrix.of_apply, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Matrix.conjTranspose_apply, hX.eq]

def lift (x : T → ℂ) (k : E) : T × E → ℂ := fun p => if p.2 = k then x p.1 else 0

lemma ptr_quad (X : Matrix (T × E) (T × E) ℂ) (x : T → ℂ) :
    star x ⬝ᵥ (partialTraceRight X *ᵥ x) = ∑ k : E, star (lift x k) ⬝ᵥ (X *ᵥ lift x k) := by
  simp only [dotProduct, Matrix.mulVec, partialTraceRight, Matrix.of_apply, Fintype.sum_prod_type,
    Pi.star_apply, lift]
  simp only [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_eq, Finset.sum_const_zero]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm

lemma ptr_posDef [Nonempty E] (X : Matrix (T × E) (T × E) ℂ) (hX : X.PosDef) :
    (partialTraceRight X).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (ptr_herm X hX.isHermitian) fun x hx => ?_
  rw [ptr_quad]
  obtain ⟨k0⟩ := ‹Nonempty E›
  have hnn : ∀ k, 0 ≤ star (lift x k) ⬝ᵥ (X *ᵥ lift x k) := fun k =>
    hX.posSemidef.dotProduct_mulVec_nonneg _
  have hpos : 0 < star (lift x k0) ⬝ᵥ (X *ᵥ lift x k0) := by
    refine hX.dotProduct_mulVec_pos ?_
    intro h; apply hx; funext i
    have := congrFun h (i, k0)
    simpa [lift] using this
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ k0))

lemma density_of (X : Matrix F F ℂ) (hX : X.PosDef) (ha : 0 < X.trace.re) :
    QAlgorithms.IsDensityMatrix ((X.trace.re)⁻¹ • X) := by
  refine ⟨(hX.smul (inv_pos.mpr ha)).posSemidef, ?_⟩
  rw [Matrix.trace_smul, trace_ofReal X hX.isHermitian, Complex.real_smul]
  simp only [Complex.ofReal_re]
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ ha.ne', Complex.ofReal_one]

theorem ptm_pd (h4 : EQ4) [Nonempty T] [Nonempty E] (X Y : Matrix (T × E) (T × E) ℂ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    finiteRelativeEntropy (partialTraceRight X) (partialTraceRight Y) ≤
      finiteRelativeEntropy X Y := by
  have ha := trace_pos X hX
  have hb := trace_pos Y hY
  have hρ : ((X.trace.re)⁻¹ • X).PosDef := hX.smul (inv_pos.mpr ha)
  have hσ : ((Y.trace.re)⁻¹ • Y).PosDef := hY.smul (inv_pos.mpr hb)
  have dρ := density_of X hX ha
  have dσ := density_of Y hY hb
  have key := h4 _ _ dρ hρ dσ hσ
  have pρ := ptr_posDef _ hρ
  have pσ := ptr_posDef _ hσ
  have eX : X = X.trace.re • ((X.trace.re)⁻¹ • X) := (smul_inv_smul₀ ha.ne' X).symm
  have eY : Y = Y.trace.re • ((Y.trace.re)⁻¹ • Y) := (smul_inv_smul₀ hb.ne' Y).symm
  have t1 : ((X.trace.re)⁻¹ • X).trace.re = 1 := by rw [dρ.2]; simp
  have t2 : ((Y.trace.re)⁻¹ • Y).trace.re = 1 := by rw [dσ.2]; simp
  have t3 : (partialTraceRight ((X.trace.re)⁻¹ • X)).trace.re = 1 := by rw [ptr_trace, t1]
  have t4 : (partialTraceRight ((Y.trace.re)⁻¹ • Y)).trace.re = 1 := by rw [ptr_trace, t2]
  generalize X.trace.re = a at *
  generalize Y.trace.re = b at *
  rw [eX, eY, ptr_smul a, ptr_smul b]
  unfold finiteRelativeEntropy
  rw [if_pos (ker_posDef _ _ (pσ.smul hb)), if_pos (ker_posDef _ _ (hσ.smul hb)),
    re_tr_scale _ _ pρ pσ a b ha hb, re_tr_scale _ _ hρ hσ a b ha hb, t1, t2, t3, t4]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_le_mul_of_nonneg_left key ha.le]

end PTM


/-! ## Stinespring dilation of a finite CPTP map from its Choi matrix -/

section Stine
open WildeQIT (partialTraceRight)
variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

lemma psd_decomp {P : Type} [Fintype P] [DecidableEq P] (C : Matrix P P ℂ) (hC : C.PosSemidef) :
    ∃ w : P → P → ℂ, ∀ p q, C p q = ∑ k, w k p * star (w k q) := by
  refine ⟨fun k p => ((Real.sqrt (hC.isHermitian.eigenvalues k) : ℝ) : ℂ) *
    (hC.isHermitian.eigenvectorUnitary : Matrix P P ℂ) p k, fun p q => ?_⟩
  have hs := hC.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  conv_lhs => rw [hs]
  simp only [Matrix.mul_apply, Matrix.mul_diagonal, Function.comp_apply, Matrix.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hl := hC.eigenvalues_nonneg k
  have hsq : ((Real.sqrt (hC.isHermitian.eigenvalues k) : ℝ) : ℂ) *
      ((Real.sqrt (hC.isHermitian.eigenvalues k) : ℝ) : ℂ) = (hC.isHermitian.eigenvalues k : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  simp only [star_mul', RCLike.star_def, Complex.conj_ofReal, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Function.comp_apply]
  have hr : (RCLike.ofReal (hC.isHermitian.eigenvalues k) : ℂ) = (hC.isHermitian.eigenvalues k : ℂ) := rfl
  rw [hr]
  linear_combination (-((hC.isHermitian.eigenvectorUnitary : Matrix P P ℂ) p k *
    (starRingEnd ℂ) ((hC.isHermitian.eigenvectorUnitary : Matrix P P ℂ) q k))) * hsq

theorem stinespring (Λ : Matrix S S ℂ → Matrix T T ℂ)
    (hlin : ∀ X, Λ X = ∑ i, ∑ j, X i j • Λ (Matrix.single i j 1))
    (hC : (Matrix.of fun p q : S × T => Λ (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef)
    (hTP : ∀ i j, (Λ (Matrix.single i j 1)).trace = if i = j then 1 else 0) :
    ∃ V : Matrix (T × (S × T)) S ℂ, Vᴴ * V = 1 ∧ ∀ X, Λ X = partialTraceRight (V * X * Vᴴ) := by
  obtain ⟨w, hw⟩ := psd_decomp _ hC
  have hC' : ∀ i j a b, Λ (Matrix.single i j 1) a b = ∑ k, w k (i, a) * star (w k (j, b)) :=
    fun i j a b => by simpa using hw (i, a) (j, b)
  refine ⟨Matrix.of fun r i => w r.2 (i, r.1), ?_, fun X => ?_⟩
  · ext i j
    have h := hTP j i
    simp only [Matrix.trace, Matrix.diag, hC', Fintype.sum_prod_type] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Matrix.one_apply]
    rw [show (if i = j then (1:ℂ) else 0) = if j = i then 1 else 0 by
      by_cases hij : i = j <;> simp [hij, eq_comm], ← h]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => mul_comm _ _
  · ext a b
    rw [hlin X]
    simp only [partialTraceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hC', Finset.mul_sum, Finset.sum_mul]
    refine Eq.symm ((Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans (Finset.sum_comm.trans
      ((Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_)))
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring

end Stine


/-! ## Finite data processing for CPTP maps (C3a core) -/

section FDPI
open WildeQIT (partialTraceRight)

lemma ptr_psd {T E : Type} [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
    (X : Matrix (T × E) (T × E) ℂ) (hX : X.PosSemidef) : (partialTraceRight X).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (ptr_herm X hX.isHermitian) fun x => by
    rw [ptr_quad]; exact Finset.sum_nonneg fun k _ => hX.dotProduct_mulVec_nonneg _

/-- Lindblad-Uhlmann monotonicity of the finite relative entropy under a finite CPTP map,
given by linearity on matrix units, a positive semidefinite Choi matrix and trace preservation. -/
theorem fdpi_tp (h4 : EQ4) {S T : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (Λ : Matrix S S ℂ → Matrix T T ℂ)
    (hlin : ∀ X, Λ X = ∑ i, ∑ j, X i j • Λ (Matrix.single i j 1))
    (hC : (Matrix.of fun p q : S × T => Λ (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef)
    (hTP : ∀ i j, (Λ (Matrix.single i j 1)).trace = if i = j then 1 else 0)
    (A B : Matrix S S ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    finiteRelativeEntropy (Λ A) (Λ B) ≤ finiteRelativeEntropy A B := by
  by_cases hk : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin
  swap
  · rw [show finiteRelativeEntropy A B = ⊤ by unfold finiteRelativeEntropy; rw [if_neg hk]]
    exact le_top
  obtain ⟨V, hV, hΛ⟩ := stinespring Λ hlin hC hTP
  rw [hΛ A, hΛ B, ← fre_iso A B hA.isHermitian hB.isHermitian V hV]
  have hX : (V * A * Vᴴ).PosSemidef := hA.mul_mul_conjTranspose_same V
  have hY : (V * B * Vᴴ).PosSemidef := hB.mul_mul_conjTranspose_same V
  have hkXY := (ker_iso A B V hV).mpr hk
  generalize V * A * Vᴴ = X at *
  generalize V * B * Vᴴ = Y at *
  have hδ0 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδpos : ∀ n : ℕ, (0:ℝ) < 1 / ((n:ℝ) + 1) := fun n => by positivity
  have hXn : ∀ n : ℕ, (X + (1 / ((n:ℝ) + 1)) • (1 : Matrix (T × (S × T)) (T × (S × T)) ℂ)).PosDef :=
    fun n => posDef_shift X hX _ (hδpos n)
  have hYn : ∀ n : ℕ, (Y + (1 / ((n:ℝ) + 1)) • (1 : Matrix (T × (S × T)) (T × (S × T)) ℂ)).PosDef :=
    fun n => posDef_shift Y hY _ (hδpos n)
  have tl : ∀ Z : Matrix (T × (S × T)) (T × (S × T)) ℂ, Tendsto (fun n : ℕ =>
      partialTraceRight (Z + (1 / ((n:ℝ) + 1)) • (1 : Matrix (T × (S × T)) (T × (S × T)) ℂ)))
      atTop (𝓝 (partialTraceRight Z)) := by
    intro Z
    simp only [ptr_add, ptr_smul]
    simpa using (tendsto_const_nhds (x := partialTraceRight Z)).add
      (hδ0.smul_const (partialTraceRight (1 : Matrix (T × (S × T)) (T × (S × T)) ℂ)))
  have l1 := P45Lsc.fre_lsc (fun n => (ptr_posDef _ (hXn n)).posSemidef)
    (fun n => (ptr_posDef _ (hYn n)).posSemidef) (ptr_psd X hX) (ptr_psd Y hY) (tl X) (tl Y)
  have l2 := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n : ℕ =>
    ptm_pd h4 _ _ (hXn n) (hYn n))
  have l3 := (fre_shift_tendsto X Y hX hY hkXY).liminf_eq
  exact l1.trans (l2.trans l3.le)

end FDPI

/-! ## Block lemma: adding a scalar block only increases Lindblad's relative entropy -/
section Block
variable {S1 T : Type} [Fintype S1] [DecidableEq S1] [Fintype T] [DecidableEq T]

def sc (a : ℂ) : Matrix Unit Unit ℂ := Matrix.of fun _ _ => a

lemma sc_alg (a : ℝ) : sc (a : ℂ) = algebraMap ℝ (Matrix Unit Unit ℂ) a := by
  ext i j; simp [sc, Matrix.algebraMap_matrix_apply]

lemma klein_sc (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    0 ≤ a * Real.log a - a * Real.log b + b - a := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h; simp; linarith
  · have hb' : 0 < b := lt_of_le_of_ne hb (fun h0 => absurd (hab h0.symm) h.ne')
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos h hb')
    rw [Real.log_div h.ne' hb'.ne', inv_div] at h1
    have h2 : a * (1 - b / a) ≤ a * (Real.log a - Real.log b) := mul_le_mul_of_nonneg_left h1 ha
    have e : a * (1 - b / a) = a - b := by field_simp
    nlinarith

variable (V1 : Matrix T S1 ℂ) (V2 : Matrix T Unit ℂ)
  (hV1 : V1ᴴ * V1 = 1) (hV2 : V2ᴴ * V2 = 1) (hV12 : V1ᴴ * V2 = 0)
include hV1 hV2 hV12

lemma hV21 : V2ᴴ * V1 = 0 := by
  have := congrArg Matrix.conjTranspose hV12
  simpa [Matrix.conjTranspose_mul] using this

lemma blk_mul (X1 Y1 : Matrix S1 S1 ℂ) (X2 Y2 : Matrix Unit Unit ℂ) :
    (V1 * X1 * V1ᴴ + V2 * X2 * V2ᴴ) * (V1 * Y1 * V1ᴴ + V2 * Y2 * V2ᴴ) =
      V1 * (X1 * Y1) * V1ᴴ + V2 * (X2 * Y2) * V2ᴴ := by
  have h21 := hV21 V1 V2 hV1 hV2 hV12
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, mul_iso _ _ V1 hV1, mul_iso _ _ V2 hV2]
  have c1 : V1 * X1 * V1ᴴ * (V2 * Y2 * V2ᴴ) = 0 := by
    rw [show V1 * X1 * V1ᴴ * (V2 * Y2 * V2ᴴ) = V1 * X1 * (V1ᴴ * V2) * Y2 * V2ᴴ by
      simp only [Matrix.mul_assoc], hV12]; simp
  have c2 : V2 * X2 * V2ᴴ * (V1 * Y1 * V1ᴴ) = 0 := by
    rw [show V2 * X2 * V2ᴴ * (V1 * Y1 * V1ᴴ) = V2 * X2 * (V2ᴴ * V1) * Y1 * V1ᴴ by
      simp only [Matrix.mul_assoc], h21]; simp
  rw [c1, c2, add_zero, zero_add]

lemma blk_mulVec1 (M : Matrix S1 S1 ℂ) (X2 : Matrix Unit Unit ℂ) (x : S1 → ℂ) :
    (V1 * M * V1ᴴ + V2 * X2 * V2ᴴ) *ᵥ (V1 *ᵥ x) = V1 *ᵥ (M *ᵥ x) := by
  have h21 := hV21 V1 V2 hV1 hV2 hV12
  rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    show V1 * M * V1ᴴ * V1 = V1 * M by rw [Matrix.mul_assoc, hV1, Matrix.mul_one],
    show V2 * X2 * V2ᴴ * V1 = 0 by rw [Matrix.mul_assoc, h21, Matrix.mul_zero],
    Matrix.zero_mulVec, add_zero, Matrix.mulVec_mulVec]

lemma blk_mulVec2 (M : Matrix S1 S1 ℂ) (X2 : Matrix Unit Unit ℂ) (y : Unit → ℂ) :
    (V1 * M * V1ᴴ + V2 * X2 * V2ᴴ) *ᵥ (V2 *ᵥ y) = V2 *ᵥ (X2 *ᵥ y) := by
  rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    show V2 * X2 * V2ᴴ * V2 = V2 * X2 by rw [Matrix.mul_assoc, hV2, Matrix.mul_one],
    show V1 * M * V1ᴴ * V2 = 0 by rw [Matrix.mul_assoc, hV12, Matrix.mul_zero],
    Matrix.zero_mulVec, zero_add, Matrix.mulVec_mulVec]

lemma iso_inj {S : Type} [Fintype S] [DecidableEq S] (V : Matrix T S ℂ) (hV : Vᴴ * V = 1) (x : S → ℂ)
    (h : V *ᵥ x = 0) : x = 0 := by
  have := congrArg (fun z => Vᴴ *ᵥ z) h
  simp only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact this

theorem fre_blk_ge (M1 M2 : Matrix S1 S1 ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    finiteRelativeEntropy M1 M2 ≤
      finiteRelativeEntropy (V1 * M1 * V1ᴴ + V2 * sc (a : ℂ) * V2ᴴ)
        (V1 * M2 * V1ᴴ + V2 * sc (b : ℂ) * V2ᴴ) := by
  by_cases hK : LinearMap.ker (V1 * M2 * V1ᴴ + V2 * sc (b : ℂ) * V2ᴴ).mulVecLin ≤
      LinearMap.ker (V1 * M1 * V1ᴴ + V2 * sc (a : ℂ) * V2ᴴ).mulVecLin
  swap
  · unfold finiteRelativeEntropy; rw [if_neg hK]; exact le_top
  have hK1 : LinearMap.ker M2.mulVecLin ≤ LinearMap.ker M1.mulVecLin := by
    intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    have h3 := hK (show V1 *ᵥ x ∈ _ by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, blk_mulVec1 V1 V2 hV1 hV2 hV12, hx,
        Matrix.mulVec_zero])
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, blk_mulVec1 V1 V2 hV1 hV2 hV12] at h3
    exact iso_inj V1 V2 hV1 hV2 hV12 V1 hV1 _ h3
  have hab : b = 0 → a = 0 := by
    intro hb0
    have h3 := hK (show V2 *ᵥ (fun _ => (1:ℂ)) ∈ _ by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, blk_mulVec2 V1 V2 hV1 hV2 hV12]
      have : sc (b : ℂ) *ᵥ (fun _ => (1:ℂ)) = 0 := by
        ext u; simp [sc, Matrix.mulVec, dotProduct, hb0]
      rw [this, Matrix.mulVec_zero])
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, blk_mulVec2 V1 V2 hV1 hV2 hV12] at h3
    have h4 := congrFun (iso_inj V1 V2 hV1 hV2 hV12 V2 hV2 _ h3) ()
    simpa [sc, Matrix.mulVec, dotProduct] using h4
  have hsa : ∀ x : ℝ, (sc (x : ℂ)).IsHermitian := by
    intro x; rw [sc_alg]; ext i j; simp [Matrix.algebraMap_matrix_apply]
  have hlog : ∀ (M : Matrix S1 S1 ℂ) (hM : M.IsHermitian) (x : ℝ),
      cfc Real.log (V1 * M * V1ᴴ + V2 * sc (x : ℂ) * V2ᴴ) =
        V1 * cfc Real.log M * V1ᴴ + V2 * sc (Real.log x : ℂ) * V2ᴴ := by
    intro M hM x
    have hH : (V1 * M * V1ᴴ + V2 * sc (x : ℂ) * V2ᴴ).IsHermitian :=
      (Matrix.isHermitian_mul_mul_conjTranspose V1 hM).add
        (Matrix.isHermitian_mul_mul_conjTranspose V2 (hsa x))
    rw [cfc_blocks _ M (sc (x : ℂ)) V1 V2 hH hM (hsa x) (fun n => pow_blocks M (sc (x : ℂ)) V1 V2
      (by rw [hV1, Matrix.one_mul]) (by rw [hV2, Matrix.one_mul]) hV12 n) Real.log Real.log_zero]
    rw [sc_alg x, cfc_algebraMap, ← sc_alg]
  unfold finiteRelativeEntropy
  rw [if_pos hK1, if_pos hK, hlog M1 h1 a, hlog M2 h2 b, blk_mul V1 V2 hV1 hV2 hV12,
    blk_mul V1 V2 hV1 hV2 hV12]
  apply ENNReal.ofReal_le_ofReal
  have e : ∀ (X Y Z W : Matrix S1 S1 ℂ) (x y z w : Matrix Unit Unit ℂ),
      V1 * X * V1ᴴ + V2 * x * V2ᴴ - (V1 * Y * V1ᴴ + V2 * y * V2ᴴ) + (V1 * Z * V1ᴴ + V2 * z * V2ᴴ)
        - (V1 * W * V1ᴴ + V2 * w * V2ᴴ) =
      V1 * (X - Y + Z - W) * V1ᴴ + V2 * (x - y + z - w) * V2ᴴ := by
    intro X Y Z W x y z w
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul]; abel
  rw [e, Matrix.trace_add, tr_iso _ V1 hV1, tr_iso _ V2 hV2, Complex.add_re]
  have hs : (sc (a : ℂ) * sc (Real.log a : ℂ) - sc (a : ℂ) * sc (Real.log b : ℂ) + sc (b : ℂ)
      - sc (a : ℂ)).trace.re = a * Real.log a - a * Real.log b + b - a := by
    simp [sc, Matrix.trace, Matrix.mul_apply, Complex.mul_re]
  rw [hs]
  linarith [klein_sc a b ha hb hab]

end Block

/-! ## Trace-nonincreasing finite maps: completion by a scalar block -/
section TNI
variable {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

def V1o (T : Type) [DecidableEq T] : Matrix (Option T) T ℂ := fun p a => if p = some a then 1 else 0
def V2o (T : Type) : Matrix (Option T) Unit ℂ := fun p _ => if p = none then 1 else 0

lemma V1o_iso : (V1o T)ᴴ * V1o T = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [V1o, Matrix.mul_apply, Matrix.one_apply]
  · simp [V1o, Matrix.mul_apply, Matrix.one_apply, h, Ne.symm h]

lemma V2o_iso : (V2o T)ᴴ * V2o T = 1 := by
  ext a b
  simp [V2o, Matrix.mul_apply, Fintype.sum_option]

lemma V12o : (V1o T)ᴴ * V2o T = 0 := by
  ext a b
  simp [V1o, V2o, Matrix.mul_apply, Fintype.sum_option]

def ext' (Γ : Matrix S S ℂ → Matrix T T ℂ) (Z : Matrix S S ℂ) : Matrix (Option T) (Option T) ℂ :=
  (V1o T) * Γ Z * (V1o T)ᴴ + (V2o T) * sc (Z.trace - (Γ Z).trace) * (V2o T)ᴴ

lemma ext'_ss (Γ : Matrix S S ℂ → Matrix T T ℂ) (Z : Matrix S S ℂ) (a b : T) :
    ext' Γ Z (some a) (some b) = Γ Z a b := by
  simp [ext', V1o, V2o, sc, Matrix.mul_apply, Fintype.sum_option]

lemma ext'_nn (Γ : Matrix S S ℂ → Matrix T T ℂ) (Z : Matrix S S ℂ) :
    ext' Γ Z none none = Z.trace - (Γ Z).trace := by
  simp [ext', V1o, V2o, sc, Matrix.mul_apply, Fintype.sum_option]

lemma ext'_sn (Γ : Matrix S S ℂ → Matrix T T ℂ) (Z : Matrix S S ℂ) (a : T) :
    ext' Γ Z (some a) none = 0 := by
  simp [ext', V1o, V2o, sc, Matrix.mul_apply, Fintype.sum_option]

lemma ext'_ns (Γ : Matrix S S ℂ → Matrix T T ℂ) (Z : Matrix S S ℂ) (b : T) :
    ext' Γ Z none (some b) = 0 := by
  simp [ext', V1o, V2o, sc, Matrix.mul_apply, Fintype.sum_option]

lemma tr_single1 (i j : S) : (Matrix.single i j (1:ℂ)).trace = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h; exact Matrix.trace_single_eq_same _ _
  · exact Matrix.trace_single_eq_of_ne _ _ _ h

lemma ext'_tp (Γ : Matrix S S ℂ → Matrix T T ℂ) (i j : S) :
    (ext' Γ (Matrix.single i j 1)).trace = if i = j then 1 else 0 := by
  rw [ext', Matrix.trace_add, tr_iso _ _ V1o_iso, tr_iso _ _ V2o_iso, ← tr_single1 i j]
  simp [sc, Matrix.trace]

lemma ext'_lin (Γ : Matrix S S ℂ → Matrix T T ℂ)
    (hlin : ∀ X, Γ X = ∑ i, ∑ j, X i j • Γ (Matrix.single i j 1)) (Z : Matrix S S ℂ) :
    ext' Γ Z = ∑ i, ∑ j, Z i j • ext' Γ (Matrix.single i j 1) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  cases p with
  | none =>
    cases q with
    | none =>
      simp only [ext'_nn]
      have hZ : Z.trace = ∑ i, ∑ j, Z i j * (Matrix.single i j (1:ℂ)).trace := by
        simp_rw [tr_single1, mul_ite, mul_one, mul_zero]
        simp [Matrix.trace, Finset.sum_ite_eq]
      rw [hZ, hlin Z, Matrix.trace_sum]
      simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    | some b => simp only [ext'_ns, mul_zero, Finset.sum_const_zero]
  | some a =>
    cases q with
    | none => simp only [ext'_sn, mul_zero, Finset.sum_const_zero]
    | some b =>
      simp only [ext'_ss]
      rw [hlin Z]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma choi_ext' (Γ : Matrix S S ℂ → Matrix T T ℂ)
    (hC : (Matrix.of fun p q : S × T => Γ (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef)
    (hN : (1 - Matrix.of fun p q : S => (Γ (Matrix.single p q 1)).trace).PosSemidef) :
    (Matrix.of fun p q : S × Option T => ext' Γ (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef := by
  set C := Matrix.of fun p q : S × T => Γ (Matrix.single p.1 q.1 1) p.2 q.2
  set N := (1 - Matrix.of fun p q : S => (Γ (Matrix.single p q 1)).trace)
  let W1 : Matrix (S × Option T) (S × T) ℂ :=
    Matrix.of fun x y => if x.1 = y.1 ∧ x.2 = some y.2 then 1 else 0
  let W2 : Matrix (S × Option T) S ℂ := Matrix.of fun x q => if x.1 = q ∧ x.2 = none then 1 else 0
  have e : (Matrix.of fun p q : S × Option T => ext' Γ (Matrix.single p.1 q.1 1) p.2 q.2) =
      W1 * C * W1ᴴ + W2 * N * W2ᴴ := by
    ext ⟨p, o⟩ ⟨q, o'⟩
    cases o <;> cases o' <;>
      simp [W1, W2, C, N, Matrix.mul_apply, Fintype.sum_prod_type, ext'_ss, ext'_nn, ext'_sn,
        ext'_ns, Matrix.one_apply, tr_single1, Matrix.sub_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ),
        map_one, map_zero, mul_ite, mul_one, mul_zero]
  rw [e]
  exact (hC.mul_mul_conjTranspose_same W1).add (hN.mul_mul_conjTranspose_same W2)

lemma hN_of (Γ : Matrix S S ℂ → Matrix T T ℂ)
    (hlin : ∀ X, Γ X = ∑ i, ∑ j, X i j • Γ (Matrix.single i j 1))
    (hC : (Matrix.of fun p q : S × T => Γ (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef)
    (hTNI : ∀ Z : Matrix S S ℂ, Z.PosSemidef → ∃ α : ℝ, 0 ≤ α ∧ Z.trace - (Γ Z).trace = α) :
    (1 - Matrix.of fun p q : S => (Γ (Matrix.single p q 1)).trace).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_one.sub
    have hH := hC.isHermitian
    ext p q
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.trace, Matrix.diag, star_sum]
    apply Finset.sum_congr rfl
    intro a _
    have := congrFun (congrFun hH (p, a)) (q, a)
    simpa [Matrix.conjTranspose_apply] using this
  · intro w
    obtain ⟨α, hα, he⟩ := hTNI (Matrix.vecMulVec (star w) w) (Matrix.posSemidef_vecMulVec_star_self w)
    have h1 : star w ⬝ᵥ ((1 - Matrix.of fun p q : S => (Γ (Matrix.single p q 1)).trace) *ᵥ w) =
        (Matrix.vecMulVec (star w) w).trace - (Γ (Matrix.vecMulVec (star w) w)).trace := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
      congr 1
      rw [hlin (Matrix.vecMulVec (star w) w)]
      simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, dotProduct, Matrix.mulVec,
        Matrix.of_apply, Matrix.vecMulVec_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      simp only [Pi.star_apply]; ring
    rw [h1, he]
    exact Complex.zero_le_real.mpr hα

theorem fdpi_tni (h4 : EQ4) [Nonempty S] (Γ : Matrix S S ℂ → Matrix T T ℂ)
    (hlin : ∀ X, Γ X = ∑ i, ∑ j, X i j • Γ (Matrix.single i j 1))
    (hC : (Matrix.of fun p q : S × T => Γ (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef)
    (hTNI : ∀ Z : Matrix S S ℂ, Z.PosSemidef → ∃ α : ℝ, 0 ≤ α ∧ Z.trace - (Γ Z).trace = α)
    (A B : Matrix S S ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hGA : (Γ A).IsHermitian) (hGB : (Γ B).IsHermitian) :
    finiteRelativeEntropy (Γ A) (Γ B) ≤ finiteRelativeEntropy A B := by
  obtain ⟨a, ha, hae⟩ := hTNI A hA
  obtain ⟨b, hb, hbe⟩ := hTNI B hB
  have h1 := fre_blk_ge (V1o T) (V2o T) V1o_iso V2o_iso V12o (Γ A) (Γ B) hGA hGB a b ha hb
  have hA' : ext' Γ A = (V1o T) * Γ A * (V1o T)ᴴ + (V2o T) * sc (a : ℂ) * (V2o T)ᴴ := by rw [ext', hae]
  have hB' : ext' Γ B = (V1o T) * Γ B * (V1o T)ᴴ + (V2o T) * sc (b : ℂ) * (V2o T)ᴴ := by rw [ext', hbe]
  rw [← hA', ← hB'] at h1
  exact h1.trans (fdpi_tp h4 (ext' Γ) (ext'_lin Γ hlin) (choi_ext' Γ hC (hN_of Γ hlin hC hTNI))
    (ext'_tp Γ) A B hA hB)

end TNI

end P45Dpi

end

end C3aPart

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

/-- Forms of a matrix with finite positive forms, restricted to a finite index set. -/
lemma psd_sub {J : Type} {M : Matrix J J ℂ} (hM : PSDForms M) (t : Finset J) :
    (M.submatrix (fun a : t => a.val) (fun a : t => a.val)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply]
    exact (psd_herm hM b.val a.val).symm
  · intro x
    set z : J → ℂ := fun j => if h : j ∈ t then x ⟨j, h⟩ else 0
    have e : star x ⬝ᵥ ((M.submatrix (fun a : t => a.val) (fun a : t => a.val)) *ᵥ x) =
        ∑ i ∈ t, ∑ j ∈ t, star (z i) * M i j * z j := by
      simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Finset.mul_sum]
      rw [← Finset.sum_coe_sort t]
      apply Finset.sum_congr rfl; intro a _
      rw [← Finset.sum_coe_sort t]
      apply Finset.sum_congr rfl; intro b _
      simp only [z, a.2, b.2, dif_pos, Pi.star_apply, Subtype.coe_eta]; ring
    rw [e]
    have h := hM t z
    exact Complex.le_def.mpr ⟨by simpa using h.2, by simpa using h.1.symm⟩

/-! ### Padding a finite block into `I` -/

def pad {I : Type} (s : Finset I) (Z : Matrix s s ℂ) : Matrix I I ℂ :=
  fun i j => if h : i ∈ s ∧ j ∈ s then Z ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

lemma pad_coe {I : Type} (s : Finset I) (Z : Matrix s s ℂ) (k l : s) : pad s Z k l = Z k l := by
  simp [pad, k.2, l.2]

lemma pad_forms {I : Type} (s : Finset I) (Z : Matrix s s ℂ) (hZ : Z.PosSemidef) :
    PSDForms (pad s Z) := by
  intro F z
  set z' : I → ℂ := fun i => if i ∈ F then z i else 0
  set g : I → I → ℂ := fun i j => star (z' i) * pad s Z i j * z' j
  set x : s → ℂ := fun k => z' k
  have hg1 : ∀ i j, i ∉ F → g i j = 0 := by intro i j h; simp [g, z', h]
  have hg2 : ∀ i j, j ∉ F → g i j = 0 := by intro i j h; simp [g, z', h]
  have hg3 : ∀ i j, i ∉ s → g i j = 0 := by intro i j h; simp [g, pad, h]
  have hg4 : ∀ i j, j ∉ s → g i j = 0 := by intro i j h; simp [g, pad, h]
  have eL : ∑ i ∈ F, ∑ j ∈ F, star (z i) * pad s Z i j * z j = ∑ i ∈ F ∪ s, ∑ j ∈ F ∪ s, g i j := by
    have e0 : ∑ i ∈ F, ∑ j ∈ F, star (z i) * pad s Z i j * z j = ∑ i ∈ F, ∑ j ∈ F ∪ s, g i j := by
      apply Finset.sum_congr rfl; intro i hi
      rw [← Finset.sum_subset (f := fun j => g i j) Finset.subset_union_left
        (fun j _ hj => hg2 i j hj)]
      apply Finset.sum_congr rfl; intro j hj; simp [g, z', hi, hj]
    rw [e0]
    exact Finset.sum_subset (f := fun i => ∑ j ∈ F ∪ s, g i j) Finset.subset_union_left
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => hg1 i j hi))
  have eR : star x ⬝ᵥ (Z *ᵥ x) = ∑ i ∈ F ∪ s, ∑ j ∈ F ∪ s, g i j := by
    rw [← Finset.sum_subset (f := fun i => ∑ j ∈ F ∪ s, g i j) Finset.subset_union_right
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => hg3 i j hi))]
    have e1 : ∀ i, ∑ j ∈ F ∪ s, g i j = ∑ j ∈ s, g i j := fun i =>
      (Finset.sum_subset (f := fun j => g i j) Finset.subset_union_right
        (fun j _ hj => hg4 i j hj)).symm
    simp only [e1]
    rw [← Finset.sum_coe_sort s]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_coe_sort s]
    apply Finset.sum_congr rfl; intro l _
    simp only [g, x, pad_coe, Pi.star_apply]; ring
  have h := hZ.dotProduct_mulVec_nonneg x
  rw [eR] at h; rw [eL]
  exact ⟨by simpa using (Complex.le_def.mp h).2.symm, by simpa using (Complex.le_def.mp h).1⟩

lemma pad_diag {I : Type} (s : Finset I) (Z : Matrix s s ℂ) :
    HasSum (fun i => pad s Z i i) Z.trace := by
  have h : HasSum (fun i => pad s Z i i) (∑ i ∈ s, pad s Z i i) :=
    hasSum_sum_of_ne_finset_zero (fun i hi => by simp [pad, hi])
  convert h using 1
  rw [← Finset.sum_coe_sort s]
  simp only [Matrix.trace, Matrix.diag, pad_coe]

lemma tc_pad {I : Type} [Countable I] (s : Finset I) (Z : Matrix s s ℂ) (hZ : Z.PosSemidef) :
    IsTraceClass (pad s Z) :=
  (psd_tc (pad_forms s Z hZ) (Complex.reCLM.hasSum (pad_diag s Z)).summable).1

lemma tc_single {I : Type} (i j : I) : IsTraceClass (Matrix.single i j (1:ℂ)) := by
  have e : Matrix.single i j (1:ℂ) = operatorCoeff (rk (bvec i) (bvec j)) := by
    ext p q
    rw [coeff_rk]
    rcases eq_or_ne p i with rfl | hp <;> rcases eq_or_ne q j with rfl | hq <;>
      simp [Matrix.single_apply, bvec, lp.single_apply, Pi.single_apply, *, Ne.symm]
  rw [e]; exact tc_rk _ _

lemma pad_single {I : Type} (s : Finset I) (i j : s) :
    pad s (Matrix.single i j (1:ℂ)) = Matrix.single (i : I) (j : I) 1 := by
  ext p q
  by_cases h : p ∈ s ∧ q ∈ s
  · simp only [pad, h, and_self, dif_pos, Matrix.single_apply]
    simp [Subtype.ext_iff, eq_comm]
  · simp only [pad, h, dif_neg, not_false_eq_true, Matrix.single_apply]
    split_ifs with h2
    · exact absurd ⟨h2.1 ▸ i.2, h2.2 ▸ j.2⟩ h
    · rfl

lemma pad_lin {I : Type} (s : Finset I) (Z : Matrix s s ℂ) :
    pad s Z = ∑ i, ∑ j, Z i j • Matrix.single (i : I) (j : I) (1:ℂ) := by
  have h := congrArg (pad s) (Matrix.matrix_eq_sum_single Z)
  rw [h]
  ext p q
  by_cases hpq : p ∈ s ∧ q ∈ s
  · simp only [pad, hpq, and_self, dif_pos, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    simp [Subtype.ext_iff, eq_comm]
  · simp only [pad, hpq, dif_neg, not_false_eq_true, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.single_apply]
    symm
    apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
    split_ifs with h2
    · exact absurd ⟨h2.1 ▸ i.2, h2.2 ▸ j.2⟩ hpq
    · simp

/-! ### The finite maps Γ_{s,t} Z = (Ψ (pad Z))_t -/

def gam {I J : Type} (Psi : Matrix I I ℂ → Matrix J J ℂ) (s : Finset I) (t : Finset J)
    (Z : Matrix s s ℂ) : Matrix t t ℂ :=
  (Psi (pad s Z)).submatrix (fun a : t => a.val) (fun a : t => a.val)

lemma gam_lin {I J : Type} (Φ : Channel I J) (s : Finset I) (t : Finset J) (Z : Matrix s s ℂ) :
    gam Φ.val s t Z = ∑ i, ∑ j, Z i j • gam Φ.val s t (Matrix.single i j 1) := by
  have hY : ∀ i j : s, IsTraceClass (Z i j • Matrix.single (i : I) (j : I) (1:ℂ)) :=
    fun i j => tc_smul _ (tc_single _ _)
  have hΦ : Φ.val (pad s Z) = ∑ i, ∑ j, Z i j • Φ.val (Matrix.single (i : I) (j : I) (1:ℂ)) := by
    rw [pad_lin, (chan_fsum Φ Finset.univ _ (fun i => tc_fsum Finset.univ _ (hY i))).2]
    apply Finset.sum_congr rfl; intro i _
    rw [(chan_fsum Φ Finset.univ _ (hY i)).2]
    apply Finset.sum_congr rfl; intro j _
    exact Φ.property.2.2.1 _ _ (tc_single _ _)
  ext a b
  simp only [gam, Matrix.submatrix_apply, hΦ, Matrix.sum_apply, Matrix.smul_apply, pad_single]

lemma gam_psd {I J : Type} [Countable I] (Φ : Channel I J) (s : Finset I) (t : Finset J)
    (Z : Matrix s s ℂ) (hZ : Z.PosSemidef) : (gam Φ.val s t Z).PosSemidef :=
  psd_sub (chan_psd Φ (pad_forms s Z hZ) (tc_pad s Z hZ)
    (Complex.reCLM.hasSum (pad_diag s Z)).summable) t

lemma gam_tni {I J : Type} [Countable I] (Φ : Channel I J) (s : Finset I) (t : Finset J)
    (Z : Matrix s s ℂ) (hZ : Z.PosSemidef) :
    ∃ α : ℝ, 0 ≤ α ∧ Z.trace - (gam Φ.val s t Z).trace = α := by
  have hP := chan_psd Φ (pad_forms s Z hZ) (tc_pad s Z hZ)
    (Complex.reCLM.hasSum (pad_diag s Z)).summable
  obtain ⟨τ, h1, h2⟩ := chan_trace Φ (tc_pad s Z hZ)
  have hτ : τ = Z.trace := h1.unique (pad_diag s Z)
  set d : J → ℝ := fun j => (Φ.val (pad s Z) j j).re
  have hd : ∀ j, Φ.val (pad s Z) j j = (d j : ℂ) := by
    intro j; apply Complex.ext <;> simp [d, (psd_diag hP j).1]
  have hdn : ∀ j, 0 ≤ d j := fun j => (psd_diag hP j).2
  have h3 : HasSum d τ.re := by simpa [d] using Complex.reCLM.hasSum h2
  have h4 : HasSum (fun j => (d j : ℂ)) (τ.re : ℂ) := by
    simpa using Complex.ofRealCLM.hasSum h3
  have hτr : τ = (τ.re : ℂ) := (h2.congr_fun ?_).unique h4
  swap; · intro j; exact (hd j).symm
  refine ⟨τ.re - ∑ j ∈ t, d j, ?_, ?_⟩
  · have := h3.summable.sum_le_tsum t (fun j _ => hdn j)
    rw [h3.tsum_eq] at this; linarith
  · rw [← hτ]
    have e : (gam Φ.val s t Z).trace = ∑ j ∈ t, (d j : ℂ) := by
      simp only [Matrix.trace, Matrix.diag, gam, Matrix.submatrix_apply]
      rw [← Finset.sum_coe_sort t]
      exact Finset.sum_congr rfl (fun a _ => hd a)
    rw [e]; push_cast; rw [← hτr]

/-- The Choi matrix of the finite compression `gam` of a channel is positive semidefinite. -/
lemma gam_choi {I J : Type} (Φ : Channel I J) (s : Finset I) (t : Finset J) (hs : s.Nonempty) :
    (Matrix.of fun p q : s × t => gam Φ.val s t (Matrix.single p.1 q.1 1) p.2 q.2).PosSemidef := by
  set n := Fintype.card s with hndef
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨⟨_, hs.choose_spec⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let e : Fin n ≃ s := (Fintype.equivFin s).symm
  set r : ℝ := (Real.sqrt n)⁻¹ with hr
  have hr2 : r * r = 1 / n := by
    rw [hr, ← mul_inv, Real.mul_self_sqrt hn'.le, one_div]
  have hr0 : 0 ≤ r := inv_nonneg.mpr (Real.sqrt_nonneg _)
  let x : Fin n → Hilbert I := fun k => ((r : ℂ)) • bvec ((e k : s) : I)
  have hxk : ∀ k, ‖x k‖ ^ 2 = 1 / n := by
    intro k
    have h1 : ‖bvec ((e k : s) : I)‖ = 1 := by simp [bvec, lp.norm_single]
    simp only [x, norm_smul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    rw [sq, hr2]
  have hx : ‖amp x‖ = 1 := by
    have h := amp_normSq x
    rw [Finset.sum_congr rfl (fun k _ => hxk k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one_div_cancel hn'.ne'] at h
    have h0 := norm_nonneg (amp x)
    nlinarith [h]
  set ξ := amp x with hξ
  have hρ := isDensity_rk ξ hx
  have hM : PSDForms (tensorApply Φ.val (operatorCoeff (rk ξ ξ))) :=
    (Φ.property.2.2.2 n ⟨_, hρ⟩).2.1
  set t' : Finset (J × Fin n) := t ×ˢ Finset.univ
  have h1 := psd_sub hM t'
  let f : s × t → t' := fun pa => ⟨(pa.2.val, e.symm pa.1), by simp [t', pa.2.2]⟩
  have h2 := (h1.submatrix f).smul (show (0:ℂ) ≤ ((n : ℝ) : ℂ) from by exact_mod_cast hn'.le)
  convert h2 using 1
  ext ⟨p, a⟩ ⟨q, b⟩
  have hsl : (fun i j => operatorCoeff (rk ξ ξ) (i, e.symm p) (j, e.symm q)) =
      (((1 / n : ℝ)) : ℂ) • Matrix.single (p : I) (q : I) (1:ℂ) := by
    funext i j
    rw [coeff_rk]
    have hxi : ∀ k (i' : I), ξ (i', k) = (r : ℂ) * (if i' = ((e k : s) : I) then 1 else 0) := by
      intro k i'
      show x k i' = _
      simp only [x, lp.coeFn_smul, Pi.smul_apply, bvec, lp.single_apply, Pi.single_apply,
        smul_eq_mul]
    rw [hxi, hxi]
    simp only [Equiv.apply_symm_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hi : i = (p : I) <;> by_cases hj : j = (q : I) <;>
      simp [hi, hj, eq_comm, ← Complex.ofReal_mul, hr2]
  simp only [Matrix.of_apply, gam, Matrix.submatrix_apply, pad_single, Matrix.smul_apply, f,
    tensorApply]
  rw [hsl, Φ.property.2.2.1 _ _ (tc_single _ _), Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ← Complex.ofReal_mul, mul_one_div_cancel hn'.ne', Complex.ofReal_one, one_mul]

/-! ### Two-colour lift of a density and convergence of truncations -/

lemma hs_congr {T α : Type} [AddCommMonoid α] [TopologicalSpace α] {f g : T → α} {x : α}
    (h : HasSum f x) (e : ∀ t, f t = g t) : HasSum g x := by
  have : f = g := funext e
  rwa [this] at h

lemma tc_slice {T A : Type} {R : Matrix (T × A) (T × A) ℂ} (h : IsTraceClass R) (a b : A) :
    IsTraceClass (fun i j => R (i, a) (j, b)) := by
  obtain ⟨e⟩ := h
  refine ⟨mkExp (fun n => slice (e.left n) a) (fun n => slice (e.right n) b) ?_ ?_⟩
  · exact Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => mul_le_mul (slice_norm _ _) (slice_norm _ _) (norm_nonneg _) (norm_nonneg _))
      e.summable
  · intro i j
    show HasSum _ (R (i, a) (j, b))
    rw [e.coefficients (i, a) (j, b)]
    exact (coeff_summable e (i, a) (j, b)).hasSum

lemma fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

lemma lift_hasSum {T : Type} (c : T → Fin 2) (f : T → ℝ) (x : ℝ) (hf : HasSum f x)
    (hf0 : ∀ t, 0 ≤ f t) :
    HasSum (fun p : T × Fin 2 => if p.2 = c p.1 then f p.1 else 0) x := by
  have hs : ∀ a : Fin 2, Summable (fun t => if a = c t then f t else 0) := fun a =>
    Summable.of_nonneg_of_le (fun t => by split_ifs <;> simp [hf0])
      (fun t => by split_ifs <;> simp [hf0]) hf.summable
  have h := hasSum_prod_fin (f := fun p : T × Fin 2 => if p.2 = c p.1 then f p.1 else 0)
    (fun a => (hs a).hasSum)
  convert h using 1
  rw [Fin.sum_univ_two]
  have h2 := (hs 0).hasSum.add (hs 1).hasSum
  refine hf.unique (by
    convert h2 using 1
    funext t
    rcases fin2_cases (c t) with hk | hk <;> simp [hk])

lemma liftv_mem {T : Type} (c : T → Fin 2) (u : Hilbert T) :
    Memℓp (fun p : T × Fin 2 => if p.2 = c p.1 then u p.1 else 0) 2 := by
  refine (memℓp_two_iff' _).mpr ?_
  have h := lift_hasSum c (fun t => ‖u t‖ ^ 2) _ (hasSum_normSq u) (fun t => sq_nonneg _)
  refine h.summable.congr (fun p => ?_)
  split_ifs <;> simp

def liftv {T : Type} (c : T → Fin 2) (u : Hilbert T) : Hilbert (T × Fin 2) :=
  ⟨fun p => if p.2 = c p.1 then u p.1 else 0, liftv_mem c u⟩

lemma liftv_apply {T : Type} (c : T → Fin 2) (u : Hilbert T) (p : T × Fin 2) :
    liftv c u p = if p.2 = c p.1 then u p.1 else 0 := rfl

lemma liftv_norm_le {T : Type} (c : T → Fin 2) (u : Hilbert T) : ‖liftv c u‖ ≤ ‖u‖ := by
  have h := lift_hasSum c (fun t => ‖u t‖ ^ 2) _ (hasSum_normSq u) (fun t => sq_nonneg _)
  have h2 : HasSum (fun p => ‖liftv c u p‖ ^ 2) (‖u‖ ^ 2) := by
    refine hs_congr h (fun p => ?_)
    rw [liftv_apply]; split_ifs <;> simp
  have h3 := (hasSum_normSq (liftv c u)).unique h2
  exact le_of_eq ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3)

def liftm {T : Type} (c : T → Fin 2) (X : Matrix T T ℂ) : Matrix (T × Fin 2) (T × Fin 2) ℂ :=
  fun p q => if p.2 = c p.1 ∧ q.2 = c q.1 then X p.1 q.1 else 0

lemma tc_liftm {T : Type} (c : T → Fin 2) {X : Matrix T T ℂ} (hX : IsTraceClass X) :
    IsTraceClass (liftm c X) := by
  obtain ⟨e⟩ := hX
  refine ⟨mkExp (fun n => liftv c (e.left n)) (fun n => liftv c (e.right n)) ?_ ?_⟩
  · exact Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => mul_le_mul (liftv_norm_le _ _) (liftv_norm_le _ _) (norm_nonneg _)
        (norm_nonneg _)) e.summable
  · intro p q
    have h := (coeff_summable e p.1 q.1).hasSum
    rw [← e.coefficients] at h
    show HasSum _ (if p.2 = c p.1 ∧ q.2 = c q.1 then X p.1 q.1 else 0)
    by_cases hp : p.2 = c p.1 <;> by_cases hq : q.2 = c q.1
    · simpa [liftv_apply, hp, hq] using h
    all_goals simp [liftv_apply, hp, hq]

lemma forms_liftm {T : Type} (c : T → Fin 2) {X : Matrix T T ℂ} (hX : PSDForms X) :
    PSDForms (liftm c X) := by
  intro F z
  set G := F.filter (fun p => p.2 = c p.1) with hG
  set g : T × Fin 2 → T × Fin 2 → ℂ := fun p q => star (z p) * liftm c X p q * z q
  have hGF : G ⊆ F := Finset.filter_subset _ _
  have e1 : ∑ p ∈ F, ∑ q ∈ F, g p q = ∑ p ∈ G, ∑ q ∈ G, g p q := by
    symm
    rw [← Finset.sum_subset hGF (fun p hp hpG => ?_)]
    · apply Finset.sum_congr rfl; intro p _
      exact Finset.sum_subset hGF (fun q hq hqG => by
        have : ¬ q.2 = c q.1 := fun h => hqG (Finset.mem_filter.mpr ⟨hq, h⟩)
        simp [g, liftm, this])
    · have : ¬ p.2 = c p.1 := fun h => hpG (Finset.mem_filter.mpr ⟨hp, h⟩)
      exact Finset.sum_eq_zero (fun q _ => by simp [g, liftm, this])
  set z' : T → ℂ := fun i => z (i, c i)
  have hinj : ∀ x ∈ G, ∀ y ∈ G, x.1 = y.1 → x = y := by
    intro x hx y hy hxy
    have h1 := (Finset.mem_filter.mp hx).2
    have h2 := (Finset.mem_filter.mp hy).2
    exact Prod.ext hxy (by rw [h1, h2, hxy])
  have hpt : ∀ p ∈ G, p = (p.1, c p.1) := fun p hp =>
    Prod.ext rfl (Finset.mem_filter.mp hp).2
  have e2 : ∑ p ∈ G, ∑ q ∈ G, g p q =
      ∑ i ∈ G.image Prod.fst, ∑ j ∈ G.image Prod.fst, star (z' i) * X i j * z' j := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl; intro p hp
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl; intro q hq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    simp only [g, liftm, z', hp', hq', and_self, if_true]
    rw [← hp', ← hq']
  rw [e1, e2]
  exact hX _ _

lemma dens_liftm {T : Type} (c : T → Fin 2) {X : Matrix T T ℂ} (hX : IsDensity X) :
    IsDensity (liftm c X) := by
  have hd : ∀ p : T × Fin 2, (liftm c X p p).re = if p.2 = c p.1 then (X p.1 p.1).re else 0 := by
    intro p; simp only [liftm, and_self]; split_ifs <;> simp
  have hs : HasSum (fun t => (X t t).re) 1 := by
    rw [← hX.2.2.2]; exact hX.2.2.1.hasSum
  have h := lift_hasSum c (fun t => (X t t).re) 1 hs (fun t => (psd_diag hX.2.1 t).2)
  have h' : HasSum (fun p => (liftm c X p p).re) 1 := hs_congr h (fun p => (hd p).symm)
  exact ⟨tc_liftm c hX.1, forms_liftm c hX.2.1, h'.summable, h'.tsum_eq⟩

lemma liftm_sum {T : Type} (c : T → Fin 2) (X : Matrix T T ℂ) :
    X = ∑ α, ∑ β, (fun i j => liftm c X (i, α) (j, β)) := by
  ext i j
  simp only [Matrix.sum_apply, liftm]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rcases fin2_cases (c i) with h1 | h1 <;> rcases fin2_cases (c j) with h2 | h2 <;> simp [h1, h2]

def cs {I : Type} (s : Finset I) (i : I) : Fin 2 := if i ∈ s then 0 else 1

lemma liftm_00 {I : Type} (s : Finset I) (X : Matrix I I ℂ) :
    (fun i j => liftm (cs s) X (i, 0) (j, 0)) =
      pad s (X.submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
  funext i j
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [liftm, cs, pad, hi, hj]

lemma diag_le_one {T : Type} {M : Matrix T T ℂ} (hM : IsDensity M) (p : T) : (M p p).re ≤ 1 := by
  have h := hM.2.2.1.sum_le_tsum {p} (fun q _ => (psd_diag hM.2.1 q).2)
  rw [hM.2.2.2, Finset.sum_singleton] at h
  exact h

/-- Quantitative truncation bound: the compression of a density to `s` changes every output
entry of a channel by at most `2 √τ + τ`, `τ = 1 - Σ_{i ∈ s} X_ii`. -/
lemma chan_trunc_bound {I J : Type} (Φ : Channel I J) (X : Matrix I I ℂ) (hX : IsDensity X)
    (s : Finset I) (a b : J) :
    ‖Φ.val X a b - Φ.val (pad s (X.submatrix (fun i : s => i.val) (fun i : s => i.val))) a b‖ ≤
      2 * Real.sqrt (1 - ∑ i ∈ s, (X i i).re) + (1 - ∑ i ∈ s, (X i i).re) := by
  set τ := 1 - ∑ i ∈ s, (X i i).re with hτ
  set R := liftm (cs s) X
  have hR : IsDensity R := dens_liftm (cs s) hX
  have hout : IsDensity (tensorApply Φ.val R) := Φ.property.2.2.2 2 ⟨R, hR⟩
  set M := tensorApply Φ.val R with hMdef
  have hM : PSDForms M := hout.2.1
  set B : Fin 2 → Fin 2 → Matrix I I ℂ := fun α β => fun i j => R (i, α) (j, β)
  have hMB : ∀ (p q : J) (α β : Fin 2), M (p, α) (q, β) = Φ.val (B α β) p q := fun _ _ _ _ => rfl
  have hBtc : ∀ α β, IsTraceClass (B α β) := fun α β => tc_slice hR.1 α β
  have hdec : Φ.val X = ∑ α, ∑ β, Φ.val (B α β) := by
    have hX' : X = ∑ α, ∑ β, B α β := liftm_sum (cs s) X
    conv_lhs => rw [hX']
    rw [(chan_fsum Φ Finset.univ _ (fun α => tc_fsum Finset.univ _ (hBtc α))).2]
    apply Finset.sum_congr rfl; intro α _
    exact (chan_fsum Φ Finset.univ _ (hBtc α)).2
  have h00 : B 0 0 = pad s (X.submatrix (fun i : s => i.val) (fun i : s => i.val)) :=
    liftm_00 s X
  -- the (1,1) block has trace τ
  have hs : HasSum (fun t => (X t t).re) 1 := by
    rw [← hX.2.2.2]; exact hX.2.2.1.hasSum
  have hXc : HasSum (fun i => X i i) 1 := by
    have h4 := Complex.ofRealCLM.hasSum hs
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one] at h4
    exact hs_congr h4 (fun i => Complex.ext (by simp) (by simp [(psd_diag hX.2.1 i).1]))
  have hS : HasSum (fun i => if i ∈ s then X i i else 0) (∑ i ∈ s, X i i) := by
    have hS0 : HasSum (fun i => if i ∈ s then X i i else 0)
        (∑ i ∈ s, (if i ∈ s then X i i else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun i hi => by simp [hi])
    have e : ∑ i ∈ s, (if i ∈ s then X i i else 0) = ∑ i ∈ s, X i i :=
      Finset.sum_congr rfl (fun i hi => by simp [hi])
    rw [e] at hS0
    exact hS0
  have hB11 : HasSum (fun i => B 1 1 i i) (1 - ∑ i ∈ s, X i i) :=
    hs_congr (hXc.sub hS) (fun i => by by_cases hi : i ∈ s <;> simp [B, R, liftm, cs, hi])
  obtain ⟨τ', h1, h2⟩ := chan_trace Φ (hBtc 1 1)
  have hτ' : τ' = 1 - ∑ i ∈ s, X i i := h1.unique hB11
  have h2r : HasSum (fun j => (Φ.val (B 1 1) j j).re) τ := by
    have h5 := Complex.reCLM.hasSum h2
    rw [hτ'] at h5
    simpa [hτ, Complex.re_sum] using h5
  have hd1 : ∀ j, 0 ≤ (Φ.val (B 1 1) j j).re := fun j => (psd_diag hM (j, 1)).2
  have hb11 : ∀ j, (Φ.val (B 1 1) j j).re ≤ τ := fun j => by
    have h6 := h2r.summable.sum_le_tsum {j} (fun q _ => hd1 q)
    rw [h2r.tsum_eq, Finset.sum_singleton] at h6
    exact h6
  have hτ0 : 0 ≤ τ := (hd1 b).trans (hb11 b)
  have hd0 : ∀ j, 0 ≤ (Φ.val (B 0 0) j j).re ∧ (Φ.val (B 0 0) j j).re ≤ 1 := fun j =>
    ⟨(psd_diag hM (j, 0)).2, diag_le_one hout (j, 0)⟩
  have c01 : ‖Φ.val (B 0 1) a b‖ ≤ Real.sqrt τ := by
    have h : ‖Φ.val (B 0 1) a b‖ ^ 2 ≤ (Φ.val (B 0 0) a a).re * (Φ.val (B 1 1) b b).re :=
      psd_cs hM (a, 0) (b, 1)
    have h' : ‖Φ.val (B 0 1) a b‖ ^ 2 ≤ τ := h.trans (by nlinarith [hd0 a, hb11 b, hd1 b])
    calc ‖Φ.val (B 0 1) a b‖ = Real.sqrt (‖Φ.val (B 0 1) a b‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt τ := Real.sqrt_le_sqrt h'
  have c10 : ‖Φ.val (B 1 0) a b‖ ≤ Real.sqrt τ := by
    have h : ‖Φ.val (B 1 0) a b‖ ^ 2 ≤ (Φ.val (B 1 1) a a).re * (Φ.val (B 0 0) b b).re :=
      psd_cs hM (a, 1) (b, 0)
    have h' : ‖Φ.val (B 1 0) a b‖ ^ 2 ≤ τ := h.trans (by nlinarith [hd0 b, hb11 a, hd1 a])
    calc ‖Φ.val (B 1 0) a b‖ = Real.sqrt (‖Φ.val (B 1 0) a b‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt τ := Real.sqrt_le_sqrt h'
  have c11 : ‖Φ.val (B 1 1) a b‖ ≤ τ := by
    have h : ‖Φ.val (B 1 1) a b‖ ^ 2 ≤ (Φ.val (B 1 1) a a).re * (Φ.val (B 1 1) b b).re :=
      psd_cs hM (a, 1) (b, 1)
    have h' : ‖Φ.val (B 1 1) a b‖ ^ 2 ≤ τ ^ 2 :=
      h.trans (by nlinarith [hb11 a, hb11 b, hd1 a, hd1 b])
    calc ‖Φ.val (B 1 1) a b‖ = Real.sqrt (‖Φ.val (B 1 1) a b‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (τ ^ 2) := Real.sqrt_le_sqrt h'
      _ = τ := Real.sqrt_sq hτ0
  rw [hdec, ← h00]
  simp only [Fin.sum_univ_two]
  have e : (Φ.val (B 0 0) + Φ.val (B 0 1) + (Φ.val (B 1 0) + Φ.val (B 1 1))) a b -
      Φ.val (B 0 0) a b = Φ.val (B 0 1) a b + Φ.val (B 1 0) a b + Φ.val (B 1 1) a b := by
    simp only [Matrix.add_apply]; ring
  rw [e]
  calc ‖Φ.val (B 0 1) a b + Φ.val (B 1 0) a b + Φ.val (B 1 1) a b‖
      ≤ ‖Φ.val (B 0 1) a b‖ + ‖Φ.val (B 1 0) a b‖ + ‖Φ.val (B 1 1) a b‖ := norm_add₃_le
    _ ≤ Real.sqrt τ + Real.sqrt τ + τ := add_le_add (add_le_add c01 c10) c11
    _ = 2 * Real.sqrt τ + τ := by ring

lemma chan_trunc_tendsto {I J : Type} (Φ : Channel I J) (X : Matrix I I ℂ) (hX : IsDensity X)
    {S : ℕ → Finset I} (hS : Tendsto S atTop atTop) (a b : J) :
    Tendsto (fun m => Φ.val (pad (S m) (X.submatrix (fun i : S m => i.val)
      (fun i : S m => i.val))) a b) atTop (𝓝 (Φ.val X a b)) := by
  have hs : HasSum (fun t => (X t t).re) 1 := by
    rw [← hX.2.2.2]; exact hX.2.2.1.hasSum
  have hτ : Tendsto (fun m => 1 - ∑ i ∈ S m, (X i i).re) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : Finset I => ∑ i ∈ s, (X i i).re) atTop (𝓝 1) := hs
    have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub (h1.comp hS)
    simpa using h2
  have hb : Tendsto (fun m => 2 * Real.sqrt (1 - ∑ i ∈ S m, (X i i).re) +
      (1 - ∑ i ∈ S m, (X i i).re)) atTop (𝓝 0) := by
    have h3 := (((Real.continuous_sqrt.tendsto 0).comp hτ).const_mul 2).add hτ
    simpa using h3
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hb
  rw [norm_sub_rev]
  exact chan_trunc_bound Φ X hX (S m) a b

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats finiteRelativeEntropy) in
/-- C3 (Lindblad-Uhlmann monotonicity) for a channel, from the finite-dimensional EQ4. -/
theorem c3_chan (h4 : P45Dpi.EQ4) {I J : Type} [Countable I] [Nonempty I] (Φ : Channel I J)
    (X Y : Matrix I I ℂ) (hX : IsDensity X) (hY : IsDensity Y) :
    extendedRelativeEntropyNats (Φ.val X) (Φ.val Y) ≤ extendedRelativeEntropyNats X Y := by
  unfold extendedRelativeEntropyNats
  refine iSup_le fun t => ?_
  obtain ⟨f, hf⟩ := exists_surjective_nat I
  set S : ℕ → Finset I := fun m => (Finset.range (m + 1)).image f with hSdef
  have hSmono : Monotone S := fun m n hmn =>
    Finset.image_subset_image (Finset.range_subset_range.mpr (by omega))
  have hS : Tendsto S atTop atTop := tendsto_atTop_finset_of_monotone hSmono (fun i =>
    ⟨(hf i).choose, Finset.mem_image.mpr ⟨(hf i).choose, Finset.mem_range.mpr (Nat.lt_succ_self _),
      (hf i).choose_spec⟩⟩)
  have hSne : ∀ m, (S m).Nonempty := fun m => ⟨f 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  have hXm : ∀ m, (X.submatrix (fun i : S m => i.val) (fun i : S m => i.val)).PosSemidef :=
    fun m => psd_sub hX.2.1 (S m)
  have hYm : ∀ m, (Y.submatrix (fun i : S m => i.val) (fun i : S m => i.val)).PosSemidef :=
    fun m => psd_sub hY.2.1 (S m)
  have hstep : ∀ m, finiteRelativeEntropy
      (gam Φ.val (S m) t (X.submatrix (fun i : S m => i.val) (fun i : S m => i.val)))
      (gam Φ.val (S m) t (Y.submatrix (fun i : S m => i.val) (fun i : S m => i.val))) ≤
      ⨆ s : Finset I, finiteRelativeEntropy (X.submatrix (fun i : s => i.val) (fun i : s => i.val))
        (Y.submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
    intro m
    have : Nonempty (S m) := (hSne m).to_subtype
    refine (P45Dpi.fdpi_tni h4 (gam Φ.val (S m) t) (gam_lin Φ (S m) t) (gam_choi Φ (S m) t (hSne m))
      (gam_tni Φ (S m) t) _ _ (hXm m) (hYm m) (gam_psd Φ (S m) t _ (hXm m)).1
      (gam_psd Φ (S m) t _ (hYm m)).1).trans ?_
    exact le_iSup (fun s : Finset I => finiteRelativeEntropy
      (X.submatrix (fun i : s => i.val) (fun i : s => i.val))
      (Y.submatrix (fun i : s => i.val) (fun i : s => i.val))) (S m)
  have hPX := psd_sub (chan_psd Φ hX.2.1 hX.1 hX.2.2.1) t
  have hPY := psd_sub (chan_psd Φ hY.2.1 hY.1 hY.2.2.1) t
  have htX : Tendsto (fun m => gam Φ.val (S m) t
      (X.submatrix (fun i : S m => i.val) (fun i : S m => i.val))) atTop
      (𝓝 ((Φ.val X).submatrix (fun a : t => a.val) (fun a : t => a.val))) :=
    tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b =>
      chan_trunc_tendsto Φ X hX hS a.val b.val
  have htY : Tendsto (fun m => gam Φ.val (S m) t
      (Y.submatrix (fun i : S m => i.val) (fun i : S m => i.val))) atTop
      (𝓝 ((Φ.val Y).submatrix (fun a : t => a.val) (fun a : t => a.val))) :=
    tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b =>
      chan_trunc_tendsto Φ Y hY hS a.val b.val
  have hlim := P45Lsc.fre_lsc (fun m => gam_psd Φ (S m) t _ (hXm m))
    (fun m => gam_psd Φ (S m) t _ (hYm m)) hPX hPY htX htY
  refine hlim.trans ?_
  exact Filter.liminf_le_of_le (by isBoundedDefault) (fun c hc =>
    let ⟨m, hm⟩ := hc.exists; hm.trans (hstep m))

end P45C3

end

end C3Part

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

open scoped ComplexOrder

theorem solution
    (h4 : ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (ρ σ : Matrix (A × B) (A × B) ℂ), QAlgorithms.IsDensityMatrix ρ → ρ.PosDef →
      QAlgorithms.IsDensityMatrix σ → σ.PosDef →
      SimpleSSA.Monotone.relEntropy (WildeQIT.partialTraceRight ρ) (WildeQIT.partialTraceRight σ) ≤
        SimpleSSA.Monotone.relEntropy ρ σ)
    {I J : Type} [Countable I] [Nonempty I] (Phi : Channel I J)
    (X Y : Matrix I I ℂ) (hX : QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity X)
    (hY : QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity Y) :
    extendedRelativeEntropyNats (Phi.val X) (Phi.val Y) ≤ extendedRelativeEntropyNats X Y := by
  exact P45C3.c3_chan h4 Phi X Y hX hY

end

end ChildRoot
