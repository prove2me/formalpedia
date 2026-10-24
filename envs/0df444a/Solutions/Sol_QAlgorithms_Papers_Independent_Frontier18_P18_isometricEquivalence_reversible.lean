-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P18.isometricEquivalence_reversible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T00:15:05.11439+00:00
-- url     : https://prove2.me/submissions/1b0bf91d-4282-4d6d-bfd5-6c5cc7c3c23e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate

attribute [local instance] Classical.propDecidable

namespace P18RevAux

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P18

/-! ## Part A: coordinates, uniqueness of bounded realizations -/

lemma hasSum_coord {I ι : Type} {f : ι → Hilbert I} {x : Hilbert I} (h : HasSum f x) (i : I) :
    HasSum (fun n => f n i) (x i) :=
  h.map (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i) (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i).continuous

lemma hasSum_basis {I : Type} (x : Hilbert I) :
    HasSum (fun j => x j • (lp.single 2 j (1 : ℂ) : Hilbert I)) x := by
  have := lp.hasSum_single (E := fun _ : I => ℂ) (p := 2) (by simp) x
  convert this using 2 with j
  rw [← lp.single_smul, smul_eq_mul, mul_one]

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

lemma bO_coeff {I : Type} (T : Hilbert I →L[ℂ] Hilbert I) :
    boundedOperator (operatorCoeff T) = T := bO_eq rfl

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

def conjExp {I L : Type} (B : Hilbert I →L[ℂ] Hilbert L) {X : Matrix I I ℂ}
    (e : NuclearExpansion X) : NuclearExpansion (conjugateCoeff B X) :=
  mkExp (fun n => B (e.left n)) (fun n => B (e.right n))
    (by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (e.summable.mul_left (‖B‖ * ‖B‖))
      calc ‖B (e.left n)‖ * ‖B (e.right n)‖ ≤ (‖B‖ * ‖e.left n‖) * (‖B‖ * ‖e.right n‖) :=
            mul_le_mul (B.le_opNorm _) (B.le_opNorm _) (norm_nonneg _) (by positivity)
        _ = ‖B‖ * ‖B‖ * (‖e.left n‖ * ‖e.right n‖) := by ring)
    (conj_hasSum B e)

/-! ## Part C: Cauchy-Schwarz on coordinates and the trace formula -/

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

lemma prodF_summable {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    Summable (fun p : ℕ × I => e.left p.1 p.2 * star (e.right p.1 p.2)) := by
  apply Summable.of_norm
  have hnn : 0 ≤ (fun p : ℕ × I => ‖e.left p.1 p.2 * star (e.right p.1 p.2)‖) :=
    fun p => norm_nonneg _
  refine (summable_prod_of_nonneg hnn).2 ⟨fun n => ?_, ?_⟩
  · simpa [norm_mul] using (cs_coord (e.left n) (e.right n)).1
  · refine Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => norm_nonneg _))
      (fun n => ?_) e.summable
    simpa [norm_mul] using (cs_coord (e.left n) (e.right n)).2

lemma trace_hasSum {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    HasSum (fun i => X i i) (∑' n, inner ℂ (e.right n) (e.left n)) := by
  have hF := prodF_summable e
  have h1 : HasSum (fun n => inner ℂ (e.right n) (e.left n)) (∑' p : ℕ × I,
      e.left p.1 p.2 * star (e.right p.1 p.2)) := by
    refine hF.hasSum.prod_fiberwise (fun n => ?_)
    have := lp.hasSum_inner (𝕜 := ℂ) (e.right n) (e.left n)
    have hfun : (fun i => e.left n i * star (e.right n i)) =
        fun i => inner ℂ (e.right n i) (e.left n i) := by
      funext i
      simp [mul_comm]
    rw [hfun]
    exact this
  rw [h1.tsum_eq]
  have hF' : Summable (fun p : I × ℕ => e.left p.2 p.1 * star (e.right p.2 p.1)) :=
    (Equiv.prodComm I ℕ).summable_iff.mpr hF
  have h2 := hF'.hasSum.prod_fiberwise (fun i => by
    have hs : Summable (fun n => e.left n i * star (e.right n i)) :=
      hF.comp_injective (i := fun n : ℕ => ((n, i) : ℕ × I)) (fun a b h => by simpa using h)
    have := hs.hasSum
    rw [← e.coefficients i i] at this
    exact this)
  convert h2 using 1
  exact ((Equiv.prodComm I ℕ).tsum_eq _).symm

lemma trace_eq {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    ∑' i, X i i = ∑' n, inner ℂ (e.right n) (e.left n) := (trace_hasSum e).tsum_eq

/-! ## Part D: finite products, slices, tensor operators, positivity -/

lemma coeff_summable {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) (i j : T) :
    Summable (fun n => e.left n i * star (e.right n j)) := by
  refine Summable.of_norm_bounded e.summable (fun n => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _)
    (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)

lemma coeff_hasSum {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) (i j : T) :
    HasSum (fun n => e.left n i * star (e.right n j)) (X i j) := by
  rw [e.coefficients i j]
  exact (coeff_summable e i j).hasSum

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

def glue {T A : Type} [Fintype A] (g : A → Hilbert T) : Hilbert (T × A) :=
  ⟨fun p => g p.2 p.1, by
    refine (memℓp_two_iff' (fun p : T × A => g p.2 p.1)).mpr ?_
    exact (hasSum_prod_fin (f := fun p : T × A => ‖(g p.2) p.1‖ ^ 2)
      (fun a => hasSum_normSq (g a))).summable⟩

@[simp] lemma glue_apply {T A : Type} [Fintype A] (g : A → Hilbert T) (p : T × A) :
    glue g p = g p.2 p.1 := rfl

lemma normSq_glue {T A : Type} [Fintype A] (g : A → Hilbert T) :
    ‖glue g‖ ^ 2 = ∑ a, ‖g a‖ ^ 2 :=
  (hasSum_normSq (glue g)).unique
    (hasSum_prod_fin (f := fun p : T × A => ‖(g p.2) p.1‖ ^ 2) (fun a => hasSum_normSq (g a)))

lemma normSq_slices {T A : Type} [Fintype A] (x : Hilbert (T × A)) :
    ‖x‖ ^ 2 = ∑ a, ‖sliceV a x‖ ^ 2 :=
  (hasSum_normSq x).unique
    (hasSum_prod_fin (f := fun p : T × A => ‖x p‖ ^ 2) (fun a => hasSum_normSq (sliceV a x)))

lemma norm_sliceV_le {T A : Type} [Fintype A] (a : A) (x : Hilbert (T × A)) :
    ‖sliceV a x‖ ≤ ‖x‖ := by
  have h2 : ‖sliceV a x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [normSq_slices x]
    exact Finset.single_le_sum (f := fun b => ‖sliceV b x‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ a)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

def sliceL {T A : Type} [Fintype A] (a : A) : Hilbert (T × A) →L[ℂ] Hilbert T :=
  LinearMap.mkContinuous
    { toFun := sliceV a
      map_add' := fun x y => by ext t; simp
      map_smul' := fun c x => by ext t; simp }
    1 (fun x => by rw [one_mul]; exact norm_sliceV_le a x)

@[simp] lemma sliceL_apply {T A : Type} [Fintype A] (a : A) (x : Hilbert (T × A)) (t : T) :
    sliceL a x t = x (t, a) := rfl

def tensV {T U A : Type} [Fintype A] (B : Hilbert T →L[ℂ] Hilbert U) (x : Hilbert (T × A)) :
    Hilbert (U × A) :=
  glue (fun a => B (sliceL a x))

lemma norm_tensV_le {T U A : Type} [Fintype A] (B : Hilbert T →L[ℂ] Hilbert U)
    (x : Hilbert (T × A)) : ‖tensV B x‖ ≤ ‖B‖ * ‖x‖ := by
  have h2 : ‖tensV B x‖ ^ 2 ≤ (‖B‖ * ‖x‖) ^ 2 := by
    rw [tensV, normSq_glue, mul_pow, normSq_slices x, Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

def tensL {T U A : Type} [Fintype A] (B : Hilbert T →L[ℂ] Hilbert U) :
    Hilbert (T × A) →L[ℂ] Hilbert (U × A) :=
  LinearMap.mkContinuous
    { toFun := tensV B
      map_add' := fun x y => by ext p; simp [tensV]
      map_smul' := fun c x => by ext p; simp [tensV] }
    ‖B‖ (fun x => norm_tensV_le B x)

@[simp] lemma tensL_apply {T U A : Type} [Fintype A] (B : Hilbert T →L[ℂ] Hilbert U)
    (x : Hilbert (T × A)) (p : U × A) : tensL B x p = B (sliceL p.2 x) p.1 := rfl

lemma summable_map_exp {T T' U U' : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X)
    (L1 : Hilbert T →L[ℂ] Hilbert U) (L2 : Hilbert T →L[ℂ] Hilbert U') :
    Summable (fun n => ‖L1 (e.left n)‖ * ‖L2 (e.right n)‖) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (e.summable.mul_left (‖L1‖ * ‖L2‖))
  calc ‖L1 (e.left n)‖ * ‖L2 (e.right n)‖ ≤ (‖L1‖ * ‖e.left n‖) * (‖L2‖ * ‖e.right n‖) :=
        mul_le_mul (L1.le_opNorm _) (L2.le_opNorm _) (norm_nonneg _) (by positivity)
    _ = ‖L1‖ * ‖L2‖ * (‖e.left n‖ * ‖e.right n‖) := by ring

def sliceExp {T A : Type} [Fintype A] {R : Matrix (T × A) (T × A) ℂ}
    (e : NuclearExpansion R) (a b : A) : NuclearExpansion (fun k k' => R (k, a) (k', b)) :=
  mkExp (fun m => sliceL a (e.left m)) (fun m => sliceL b (e.right m))
    (summable_map_exp (T' := T) e (sliceL a) (sliceL b))
    (fun k k' => coeff_hasSum e (k, a) (k', b))

def ampExp {T U A : Type} [Fintype A] (B : Hilbert T →L[ℂ] Hilbert U)
    {R : Matrix (T × A) (T × A) ℂ} (e : NuclearExpansion R) :
    NuclearExpansion (tensorApply (conjugateCoeff B) R) :=
  mkExp (fun m => tensL B (e.left m)) (fun m => tensL B (e.right m))
    (summable_map_exp (T' := T) e (tensL B) (tensL B))
    (fun p q => conj_hasSum B (sliceExp e p.2 q.2) p.1 q.1)

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

lemma formG_hasSum {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) (y : Hilbert T) :
    HasSum (fun n => inner ℂ (e.right n) y * inner ℂ y (e.left n)) (inner ℂ y (nucOp e y)) := by
  have h2 : HasSum (fun n => inner ℂ y (inner ℂ (e.right n) y • e.left n))
      (inner ℂ y (nucOp e y)) :=
    (nucOp_hasSum e y).map (innerSL ℂ y) (innerSL ℂ y).continuous
  convert h2 using 1
  funext n
  rw [inner_smul_right]

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

lemma amp_formG {T U A : Type} [Fintype A] (B : Hilbert T →L[ℂ] Hilbert U)
    {R : Matrix (T × A) (T × A) ℂ} (e : NuclearExpansion R) (y : Hilbert (U × A)) :
    inner ℂ y (nucOp (ampExp B e) y) =
      inner ℂ (ContinuousLinearMap.adjoint (tensL B) y)
        (nucOp e (ContinuousLinearMap.adjoint (tensL B) y)) := by
  refine (formG_hasSum (ampExp B e) y).unique ?_
  convert formG_hasSum e (ContinuousLinearMap.adjoint (tensL B) y) using 1
  funext n
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  rfl

lemma amp_pos {T U A : Type} [Fintype A] (B : Hilbert T →L[ℂ] Hilbert U)
    {R : Matrix (T × A) (T × A) ℂ} (e : NuclearExpansion R) (hR : PSDForms R)
    (y : Hilbert (U × A)) :
    (inner ℂ y (nucOp (ampExp B e) y)).im = 0 ∧ 0 ≤ (inner ℂ y (nucOp (ampExp B e) y)).re := by
  rw [amp_formG]
  exact pos_ext e hR _

/-! ## Part E: sums of expansions, finite rank, the corrected channel -/

def ileave {β : Type} (f g : ℕ → β) (m : ℕ) : β := if m % 2 = 0 then f (m / 2) else g (m / 2)

lemma ileave_even {β : Type} (f g : ℕ → β) (k : ℕ) : ileave f g (2 * k) = f k := by
  simp [ileave, show (2 * k) % 2 = 0 by omega, show 2 * k / 2 = k by omega]

lemma ileave_odd {β : Type} (f g : ℕ → β) (k : ℕ) : ileave f g (2 * k + 1) = g k := by
  simp [ileave, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]

def expAdd {T : Type} {X Y : Matrix T T ℂ} (e1 : NuclearExpansion X) (e2 : NuclearExpansion Y) :
    NuclearExpansion (X + Y) :=
  mkExp (ileave e1.left e2.left) (ileave e1.right e2.right)
    (by
      refine (HasSum.even_add_odd (f := fun m => ‖ileave e1.left e2.left m‖ *
        ‖ileave e1.right e2.right m‖) (m := ∑' n, ‖e1.left n‖ * ‖e1.right n‖)
        (m' := ∑' n, ‖e2.left n‖ * ‖e2.right n‖) ?_ ?_).summable
      · simpa only [ileave_even] using e1.summable.hasSum
      · simpa only [ileave_odd] using e2.summable.hasSum)
    (fun i j => by
      refine HasSum.even_add_odd (f := fun m => ileave e1.left e2.left m i *
        star (ileave e1.right e2.right m j)) ?_ ?_
      · simpa only [ileave_even] using coeff_hasSum e1 i j
      · simpa only [ileave_odd] using coeff_hasSum e2 i j)

lemma hasSum_fin_support {α : Type} [AddCommMonoid α] [TopologicalSpace α] {n : ℕ} (F : ℕ → α)
    (hF : ∀ m, n ≤ m → F m = 0) : HasSum F (∑ i : Fin n, F i) := by
  rw [Fin.sum_univ_eq_sum_range]
  exact hasSum_sum_of_ne_finset_zero (fun m hm => hF m (by simpa using hm))

def finL {T : Type} {n : ℕ} (f : Fin n → Hilbert T) (m : ℕ) : Hilbert T :=
  if h : m < n then f ⟨m, h⟩ else 0

lemma finL_coe {T : Type} {n : ℕ} (f : Fin n → Hilbert T) (b : Fin n) : finL f b = f b := by
  simp [finL]

lemma finL_ge {T : Type} {n : ℕ} (f : Fin n → Hilbert T) (m : ℕ) (hm : n ≤ m) : finL f m = 0 := by
  simp [finL, not_lt.mpr hm]

def finExp {T : Type} {n : ℕ} (f g : Fin n → Hilbert T) :
    NuclearExpansion (fun p q => ∑ b : Fin n, f b p * star (g b q)) :=
  mkExp (finL f) (finL g)
    ((hasSum_fin_support (n := n) (fun m => ‖finL f m‖ * ‖finL g m‖)
      (fun m hm => by simp [finL_ge f m hm])).summable)
    (fun p q => by
      have := hasSum_fin_support (n := n) (fun m => finL f m p * star (finL g m q))
        (fun m hm => by simp [finL_ge f m hm])
      simpa only [finL_coe] using this)

def qOp {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) : Hilbert T →L[ℂ] Hilbert T :=
  ContinuousLinearMap.id ℂ (Hilbert T) - (ContinuousLinearMap.adjoint B).comp B

def corrT {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) (Y : Matrix T T ℂ) : ℂ :=
  ∑' k, conjugateCoeff (qOp B) Y k k

def chanC {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) (u0 : U) (Y : Matrix T T ℂ) :
    Matrix U U ℂ :=
  conjugateCoeff B Y + corrT B Y • rankOne (lp.single 2 u0 (1:ℂ) : Hilbert U)

lemma inner_BQ {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U)
    (hP : ((ContinuousLinearMap.adjoint B).comp B).comp ((ContinuousLinearMap.adjoint B).comp B)
      = (ContinuousLinearMap.adjoint B).comp B) (u v : Hilbert T) :
    inner ℂ (B v) (B u) + inner ℂ (qOp B v) (qOp B u) = inner ℂ v u := by
  set P := (ContinuousLinearMap.adjoint B).comp B with hPdef
  have hq : ∀ x, qOp B x = x - P x := fun x => rfl
  have h1 : ∀ x y, inner ℂ (P x) y = inner ℂ (B x) (B y) := fun x y => by
    simp [P, ContinuousLinearMap.adjoint_inner_left]
  have h2 : ∀ x y, inner ℂ x (P y) = inner ℂ (B x) (B y) := fun x y => by
    simp [P, ContinuousLinearMap.adjoint_inner_right]
  have h3 : inner ℂ (P v) (P u) = inner ℂ (B v) (B u) := by
    rw [h1, ← h2]
    have : P (P u) = P u := by
      have := congrArg (fun L => L u) hP
      simpa using this
    rw [this, h2]
  rw [hq, hq, inner_sub_left, inner_sub_right, inner_sub_right, h3, h1, h2]
  ring

lemma inner_summable {T : Type} {X : Matrix T T ℂ} (e : NuclearExpansion X) :
    Summable (fun n => inner ℂ (e.right n) (e.left n)) := by
  refine Summable.of_norm_bounded e.summable (fun n => ?_)
  rw [mul_comm]
  exact norm_inner_le_norm _ _

lemma trace_conj {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) {X : Matrix T T ℂ}
    (e : NuclearExpansion X) :
    HasSum (fun k => conjugateCoeff B X k k) (∑' n, inner ℂ (B (e.right n)) (B (e.left n))) :=
  trace_hasSum (conjExp B e)

lemma rankOne_single {U : Type} (u0 i j : U) :
    rankOne (lp.single 2 u0 (1:ℂ) : Hilbert U) i j =
      (if i = u0 then 1 else 0) * (if j = u0 then 1 else 0) := by
  simp only [rankOne, lp.single_apply, Pi.single_apply]
  by_cases hj : j = u0 <;> simp [hj]

lemma trace_chanC {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U)
    (hP : ((ContinuousLinearMap.adjoint B).comp B).comp ((ContinuousLinearMap.adjoint B).comp B)
      = (ContinuousLinearMap.adjoint B).comp B) (u0 : U) {Y : Matrix T T ℂ}
    (e : NuclearExpansion Y) : HasSum (fun j => chanC B u0 Y j j) (∑' k, Y k k) := by
  have hA := trace_conj B e
  have hB : HasSum (fun j => corrT B Y * rankOne (lp.single 2 u0 (1:ℂ) : Hilbert U) j j)
      (corrT B Y) := by
    have := (hasSum_ite_eq u0 (1:ℂ)).mul_left (corrT B Y)
    rw [mul_one] at this
    have hfun : (fun j => corrT B Y * rankOne (lp.single 2 u0 (1:ℂ) : Hilbert U) j j) =
        fun j => corrT B Y * (if j = u0 then 1 else 0) := by
      funext j
      by_cases h : j = u0 <;> simp [rankOne_single, h]
    rw [hfun]
    exact this
  have hsum := hA.add hB
  have hval : (∑' n, inner ℂ (B (e.right n)) (B (e.left n))) + corrT B Y = ∑' k, Y k k := by
    have hs1 : Summable (fun n => inner ℂ (B (e.right n)) (B (e.left n))) :=
      inner_summable (conjExp B e)
    have hs2 : Summable (fun n => inner ℂ (qOp B (e.right n)) (qOp B (e.left n))) :=
      inner_summable (conjExp (qOp B) e)
    rw [corrT, (trace_conj (qOp B) e).tsum_eq, trace_eq e, ← hs1.tsum_add hs2]
    congr 1
    funext n
    exact inner_BQ B hP (e.left n) (e.right n)
  rw [hval] at hsum
  exact hsum

/-! ## Part F: channel properties of the corrected map -/

lemma operatorCoeff_add {T L : Type} (S1 S2 : Hilbert T →L[ℂ] Hilbert L) :
    operatorCoeff (S1 + S2) = operatorCoeff S1 + operatorCoeff S2 := by
  funext i j
  simp [operatorCoeff_apply]

lemma operatorCoeff_smul {T L : Type} (c : ℂ) (S : Hilbert T →L[ℂ] Hilbert L) :
    operatorCoeff (c • S) = c • operatorCoeff S := by
  funext i j
  simp [operatorCoeff_apply]

lemma conj_add {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) {X Y : Matrix T T ℂ}
    (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    conjugateCoeff B (X + Y) = conjugateCoeff B X + conjugateCoeff B Y := by
  obtain ⟨e1⟩ := hX
  obtain ⟨e2⟩ := hY
  have h : boundedOperator (X + Y) = nucOp e1 + nucOp e2 :=
    bO_eq (by rw [operatorCoeff_add, nucOp_coeff, nucOp_coeff])
  simp only [conjugateCoeff, h, bO_nuc e1, bO_nuc e2, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add, operatorCoeff_add]

lemma conj_smul {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) (c : ℂ) {X : Matrix T T ℂ}
    (hX : IsTraceClass X) : conjugateCoeff B (c • X) = c • conjugateCoeff B X := by
  obtain ⟨e1⟩ := hX
  have h : boundedOperator (c • X) = c • nucOp e1 :=
    bO_eq (by rw [operatorCoeff_smul, nucOp_coeff])
  simp only [conjugateCoeff, h, bO_nuc e1, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, operatorCoeff_smul]

lemma corrT_add {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) {X Y : Matrix T T ℂ}
    (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    corrT B (X + Y) = corrT B X + corrT B Y := by
  obtain ⟨e1⟩ := hX
  obtain ⟨e2⟩ := hY
  unfold corrT
  rw [conj_add (qOp B) ⟨e1⟩ ⟨e2⟩]
  exact (trace_conj (qOp B) e1).summable.tsum_add (trace_conj (qOp B) e2).summable

lemma corrT_smul {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) (c : ℂ) {X : Matrix T T ℂ}
    (hX : IsTraceClass X) : corrT B (c • X) = c * corrT B X := by
  unfold corrT
  rw [conj_smul (qOp B) c hX]
  exact tsum_mul_left

lemma chanC_add {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) (u0 : U) {X Y : Matrix T T ℂ}
    (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    chanC B u0 (X + Y) = chanC B u0 X + chanC B u0 Y := by
  unfold chanC
  rw [conj_add B hX hY, corrT_add B hX hY, add_smul]
  abel

lemma chanC_smul {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) (u0 : U) (c : ℂ)
    {X : Matrix T T ℂ} (hX : IsTraceClass X) : chanC B u0 (c • X) = c • chanC B u0 X := by
  unfold chanC
  rw [conj_smul B c hX, corrT_smul B c hX, smul_add, mul_smul]

lemma rank1_eq {U : Type} (c : ℂ) (u : Hilbert U) :
    c • rankOne u = fun p q => ∑ b : Fin 1, (fun _ : Fin 1 => c • u) b p *
      star ((fun _ : Fin 1 => u) b q) := by
  funext p q
  simp [rankOne, mul_assoc]

lemma chanC_tc {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U) (u0 : U) {Y : Matrix T T ℂ}
    (hY : IsTraceClass Y) : IsTraceClass (chanC B u0 Y) := by
  obtain ⟨e⟩ := hY
  unfold chanC
  rw [rank1_eq]
  exact ⟨expAdd (conjExp B e) (finExp _ _)⟩

lemma amp_form {T U A : Type} [Fintype A] (B : Hilbert T →L[ℂ] Hilbert U)
    {R : Matrix (T × A) (T × A) ℂ} (e : NuclearExpansion R) (hR : PSDForms R) :
    PSDForms (tensorApply (conjugateCoeff B) R) := by
  intro s z
  have hf := form_eq (nucOp (ampExp B e)) s id z
  rw [nucOp_coeff] at hf
  simp only [id] at hf
  rw [hf]
  exact amp_pos B e hR _

lemma corr_form {T U A : Type} [Fintype A] (Bq : Hilbert T →L[ℂ] Hilbert T)
    {R : Matrix (T × A) (T × A) ℂ} (e : NuclearExpansion R) (hR : PSDForms R)
    (c : A → A → ℂ)
    (hc : ∀ a b, HasSum (fun k => tensorApply (conjugateCoeff Bq) R (k, a) (k, b)) (c a b))
    (δ : U → ℂ) : PSDForms (fun p q : U × A => c p.2 q.2 * (δ p.1 * star (δ q.1))) := by
  intro s z
  have hG : ∀ k : T, (∑ p ∈ s, ∑ q ∈ s, star (star (δ p.1) * z p) *
      tensorApply (conjugateCoeff Bq) R (k, p.2) (k, q.2) * (star (δ q.1) * z q)).im = 0 ∧
      0 ≤ (∑ p ∈ s, ∑ q ∈ s, star (star (δ p.1) * z p) *
      tensorApply (conjugateCoeff Bq) R (k, p.2) (k, q.2) * (star (δ q.1) * z q)).re := by
    intro k
    have hf := form_eq (nucOp (ampExp Bq e)) s (fun p : U × A => ((k, p.2) : T × A))
      (fun p => star (δ p.1) * z p)
    rw [nucOp_coeff] at hf
    rw [hf]
    exact amp_pos Bq e hR _
  have hsum : HasSum (fun k : T => ∑ p ∈ s, ∑ q ∈ s, star (star (δ p.1) * z p) *
      tensorApply (conjugateCoeff Bq) R (k, p.2) (k, q.2) * (star (δ q.1) * z q))
      (∑ p ∈ s, ∑ q ∈ s, star (z p) * (c p.2 q.2 * (δ p.1 * star (δ q.1))) * z q) := by
    refine hasSum_sum (fun p _ => hasSum_sum (fun q _ => ?_))
    have h1 := ((hc p.2 q.2).mul_left (δ p.1 * star (z p))).mul_right (star (δ q.1) * z q)
    have hfun : (fun k => star (star (δ p.1) * z p) *
        tensorApply (conjugateCoeff Bq) R (k, p.2) (k, q.2) * (star (δ q.1) * z q)) =
        (fun k => δ p.1 * star (z p) * tensorApply (conjugateCoeff Bq) R (k, p.2) (k, q.2) *
          (star (δ q.1) * z q)) := by
      funext k
      simp only [star_mul, star_star]
      ring
    rw [hfun, show star (z p) * (c p.2 q.2 * (δ p.1 * star (δ q.1))) * z q =
      δ p.1 * star (z p) * c p.2 q.2 * (star (δ q.1) * z q) by ring]
    exact h1
  refine ⟨?_, ?_⟩
  · have him := Complex.hasSum_im hsum
    have hz : (fun k : T => (∑ p ∈ s, ∑ q ∈ s, star (star (δ p.1) * z p) *
        tensorApply (conjugateCoeff Bq) R (k, p.2) (k, q.2) * (star (δ q.1) * z q)).im) =
        fun _ => (0 : ℝ) := funext (fun k => (hG k).1)
    rw [hz] at him
    exact him.unique hasSum_zero
  · exact (Complex.hasSum_re hsum).nonneg (fun k => (hG k).2)

lemma chanC_density {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U)
    (hP : ((ContinuousLinearMap.adjoint B).comp B).comp ((ContinuousLinearMap.adjoint B).comp B)
      = (ContinuousLinearMap.adjoint B).comp B) (u0 : U) (n : ℕ) (rho : State (T × Fin n)) :
    IsDensity (tensorApply (chanC B u0) rho.coefficients) := by
  obtain ⟨e⟩ := rho.density.1
  have hR : PSDForms rho.coefficients := rho.density.2.1
  have htr := rho.density.2.2.2
  set R := rho.coefficients with hRdef
  let δ : Hilbert U := lp.single 2 u0 1
  let c : Fin n → Fin n → ℂ := fun a b => corrT B (fun k k' => R (k, a) (k', b))
  let Corr : Matrix (U × Fin n) (U × Fin n) ℂ := fun p q => c p.2 q.2 * rankOne δ p.1 q.1
  have hsplit : tensorApply (chanC B u0) R = tensorApply (conjugateCoeff B) R + Corr := by
    funext p q
    rfl
  let f : Fin n → Hilbert (U × Fin n) := fun b => glue (fun a => c a b • δ)
  let g : Fin n → Hilbert (U × Fin n) := fun b => glue (fun a => if a = b then δ else 0)
  have hCorr : Corr = fun p q => ∑ b : Fin n, f b p * star (g b q) := by
    funext p q
    rw [Finset.sum_eq_single q.2]
    · simp [f, g, Corr, rankOne, mul_assoc]
    · intro b _ hb
      simp [g, Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit, hCorr]
    exact ⟨expAdd (ampExp B e) (finExp f g)⟩
  · intro s z
    rw [hsplit]
    have hM := amp_form B e hR s z
    have hC := corr_form (qOp B) e hR c
      (fun a b => (trace_conj (qOp B) (sliceExp e a b)).summable.hasSum) (fun j => δ j) s z
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, Complex.add_im,
      Complex.add_re]
    refine ⟨?_, add_nonneg hM.2 ?_⟩
    · rw [hM.1]
      simpa [Corr, rankOne] using hC.1
    · simpa [Corr, rankOne] using hC.2
  · have hX : HasSum (fun p : U × Fin n => tensorApply (chanC B u0) R p p)
        (∑ a, ∑' k, R (k, a) (k, a)) :=
      hasSum_prod_fin (f := fun p : U × Fin n => tensorApply (chanC B u0) R p p)
        (fun a => by
          have := trace_chanC B hP u0 (sliceExp e a a)
          simp only [tensorApply]
          exact this)
    have hRt : HasSum (fun p : T × Fin n => R p p) (∑ a, ∑' k, R (k, a) (k, a)) :=
      hasSum_prod_fin (f := fun p : T × Fin n => R p p)
        (fun a => (trace_hasSum (sliceExp e a a)).summable.hasSum)
    have hre := Complex.hasSum_re hRt
    rw [hre.tsum_eq] at htr
    have hXre := Complex.hasSum_re hX
    rw [htr] at hXre
    exact ⟨hXre.summable, hXre.tsum_eq⟩

lemma chanC_channel {T U : Type} (B : Hilbert T →L[ℂ] Hilbert U)
    (hP : ((ContinuousLinearMap.adjoint B).comp B).comp ((ContinuousLinearMap.adjoint B).comp B)
      = (ContinuousLinearMap.adjoint B).comp B) (u0 : U) :
    IsTraceClassChannel (chanC B u0) :=
  ⟨fun _ hX => chanC_tc B u0 hX, fun _ _ hX hY => chanC_add B u0 hX hY,
    fun c _ hX => chanC_smul B u0 c hX, fun n rho => chanC_density B hP u0 n rho⟩

lemma comp_channel {I J K : Type} {C : Matrix K K ℂ → Matrix J J ℂ}
    {Psi : Matrix J J ℂ → Matrix I I ℂ} (hC : IsTraceClassChannel C)
    (hPsi : IsTraceClassChannel Psi) : IsTraceClassChannel (Psi ∘ C) := by
  refine ⟨fun X hX => hPsi.1 _ (hC.1 X hX), fun X Y hX hY => ?_, fun c X hX => ?_,
    fun n rho => ?_⟩
  · simp only [Function.comp]
    rw [hC.2.1 X Y hX hY, hPsi.2.1 _ _ (hC.1 X hX) (hC.1 Y hY)]
  · simp only [Function.comp]
    rw [hC.2.2.1 c X hX, hPsi.2.2.1 c _ (hC.1 X hX)]
  · exact hPsi.2.2.2 n ⟨tensorApply C rho.coefficients, hC.2.2.2 n rho⟩

lemma conj_conj_zero {T V : Type} (A : Hilbert V →L[ℂ] Hilbert T)
    (Q : Hilbert T →L[ℂ] Hilbert T) (hQA : Q.comp A = 0) (X : Matrix V V ℂ) :
    conjugateCoeff Q (conjugateCoeff A X) = 0 := by
  have h : boundedOperator (conjugateCoeff A X) =
      A.comp ((boundedOperator X).comp (ContinuousLinearMap.adjoint A)) := bO_coeff _
  show operatorCoeff (Q.comp ((boundedOperator (conjugateCoeff A X)).comp
    (ContinuousLinearMap.adjoint Q))) = 0
  rw [h, ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hQA]
  simp only [ContinuousLinearMap.zero_comp]
  rfl

lemma one_dir {I J K : Type} (u0 : J) (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (Phi' : Matrix I I ℂ → Matrix K K ℂ)
    (A : Hilbert J →L[ℂ] Hilbert K) (B : Hilbert K →L[ℂ] Hilbert J)
    (hP : ((ContinuousLinearMap.adjoint B).comp B).comp ((ContinuousLinearMap.adjoint B).comp B)
      = (ContinuousLinearMap.adjoint B).comp B)
    (hQA : (qOp B).comp A = 0)
    (h1 : ∀ X, IsTraceClass X → Phi' X = conjugateCoeff A (Phi X))
    (h2 : ∀ X, IsTraceClass X → Phi X = conjugateCoeff B (Phi' X))
    (S : Set (State I)) : ReversibleOn Phi S → ReversibleOn Phi' S := by
  rintro ⟨Psi, hPsi, hrec⟩
  refine ⟨Psi ∘ chanC B u0, comp_channel (chanC_channel B hP u0) hPsi, fun rho hrho => ?_⟩
  have htc := rho.density.1
  have hz : corrT B (Phi' rho.coefficients) = 0 := by
    unfold corrT
    rw [h1 _ htc, conj_conj_zero A (qOp B) hQA]
    simp
  have hC : chanC B u0 (Phi' rho.coefficients) = Phi rho.coefficients := by
    unfold chanC
    rw [hz, zero_smul, add_zero, ← h2 _ htc]
  simp only [Function.comp]
  rw [hC]
  exact hrec rho hrho

end P18RevAux

open QAlgorithms.RealRegisters (Hilbert) in
open QAlgorithms.Papers.Independent.Frontier18.P18 in
theorem solution
    {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (PhiPrime : Matrix I I ℂ → Matrix K K ℂ)
    (hPhi : QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel Phi)
    (hPhiPrime : QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel PhiPrime)
    (hEquiv : IsometricallyEquivalent Phi PhiPrime) (S : Set (QAlgorithms.Papers.Independent.Dependency50.P33.State I)) :
    ReversibleOn Phi S ↔ ReversibleOn PhiPrime S := by
  obtain ⟨W, hW, hW2⟩ := hEquiv
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  obtain ⟨k0⟩ := (inferInstance : Nonempty K)
  have hWx : ∀ x, W (ContinuousLinearMap.adjoint W (W x)) = W x := fun x => by
    have := congrArg (fun L => L x) hW
    simpa using this
  have hWs : (ContinuousLinearMap.adjoint W).comp (W.comp (ContinuousLinearMap.adjoint W)) =
      ContinuousLinearMap.adjoint W := by
    have := congrArg ContinuousLinearMap.adjoint hW
    simpa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc] using this
  have hWsx : ∀ y, ContinuousLinearMap.adjoint W (W (ContinuousLinearMap.adjoint W y)) =
      ContinuousLinearMap.adjoint W y := fun y => by
    have := congrArg (fun L => L y) hWs
    simpa using this
  constructor
  · refine P18RevAux.one_dir j0 Phi PhiPrime W (ContinuousLinearMap.adjoint W) ?_ ?_
      (fun X hX => (hW2 X hX).1) (fun X hX => (hW2 X hX).2) S
    · ext1 x
      simp [hWx]
    · ext1 y
      simp [P18RevAux.qOp, hWx]
  · refine P18RevAux.one_dir k0 PhiPrime Phi (ContinuousLinearMap.adjoint W) W ?_ ?_
      (fun X hX => (hW2 X hX).2) (fun X hX => (hW2 X hX).1) S
    · ext1 x
      simp [hWsx]
    · ext1 y
      simp [P18RevAux.qOp, hWsx]
