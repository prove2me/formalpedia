-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P19.flaggedProduct_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:31:46.74247+00:00
-- url     : https://prove2.me/submissions/80dba6a5-ea23-4964-88c7-b4172c9af6b5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

open scoped Matrix ComplexConjugate ComplexOrder
open Matrix Polynomial

namespace X8P19

theorem x8_pow {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℂ)
    (h : A = W * diagonal d * Wᴴ) (n : ℕ) : A ^ n = W * diagonal (d ^ n) * Wᴴ := by
  induction n with
  | zero => simp [hW2]
  | succ n ih =>
    rw [pow_succ, ih, h]
    have : W * diagonal (d ^ n) * Wᴴ * (W * diagonal d * Wᴴ) =
        W * (diagonal (d ^ n) * (Wᴴ * W) * diagonal d) * Wᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, hW1, Matrix.mul_one, diagonal_mul_diagonal, pow_succ]
    rfl

theorem x8_aeval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (p : ℝ[X]) :
    aeval A p = W * diagonal (fun k => ((p.eval (d k) : ℝ) : ℂ)) * Wᴴ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    congr 3; ext k; simp
  | monomial n c =>
    rw [aeval_monomial, x8_pow A W hW1 hW2 _ h n]
    simp only [eval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← diagonal_smul]
    congr 3; ext k; simp [Pi.pow_apply]

theorem x8_trace_cfc {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ k, ((f (d k) : ℝ) : ℂ) := by
  classical
  let S : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hA.eigenvalues
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A := by
    apply cfc_congr
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))).symm
  rw [h1, cfc_polynomial p A, x8_aeval A W hW1 hW2 d h p, Matrix.trace_mul_cycle, hW1,
    Matrix.one_mul, trace_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]

theorem x8_spec {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix α α ℂ) *
      diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

theorem x8_U1 {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix α α ℂ) = 1 :=
  Unitary.coe_star_mul_self _

theorem x8_sum_eig {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian)
    (ht : A.trace = 1) : ∑ k, hA.eigenvalues k = 1 := by
  have := hA.trace_eq_sum_eigenvalues
  rw [ht] at this
  have h2 := congrArg Complex.re this
  simpa [Complex.re_sum] using h2.symm

theorem x8_flog (x y : ℝ) : x * y * Real.log (x * y) =
    x * (y * Real.log y) + y * (x * Real.log x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [Real.log_mul hx hy]; ring

/-- herm from a decomposition with real diagonal -/
theorem x8_herm {ι κ : Type*} [Fintype κ] [DecidableEq κ] (W : Matrix ι κ ℂ) (d : κ → ℝ) :
    (W * diagonal (fun k => (d k : ℂ)) * Wᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  ext k; simp

/-- entropy from a unitary decomposition, any DecidableEq instance -/
theorem x8_ent {ι : Type*} [Fintype ι] [DecidableEq ι] (A W : Matrix ι ι ℂ) (hW1 : Wᴴ * W = 1)
    (d : ι → ℝ) (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy A = -∑ k, d k * Real.log (d k) := by
  have hW2 : W * Wᴴ = 1 := mul_eq_one_comm.1 hW1
  unfold QAlgorithms.Papers.Independent.Information100.P56.entropy
  rw [x8_trace_cfc A (h ▸ x8_herm W d) W hW1 hW2 d h]
  simp [Complex.re_sum]

/-- flag decomposition -/
def x8W {I L : Type} (V : L → Matrix I I ℂ) (F : Matrix L L ℂ) : Matrix (I × L) (I × L) ℂ :=
  fun x k => V k.2 x.1 k.1 * F x.2 k.2

theorem x8_W1 {I L : Type} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
    (V : L → Matrix I I ℂ) (hV : ∀ l, (V l)ᴴ * V l = 1) (F : Matrix L L ℂ) (hF : Fᴴ * F = 1) :
    (x8W V F)ᴴ * x8W V F = 1 := by
  ext k k'
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [conjTranspose_apply, x8W, star_mul']
  have hF' : ∀ l l', ∑ m, star (F m l) * F m l' = if l = l' then 1 else 0 := by
    intro l l'
    have := congrFun (congrFun hF l) l'
    rw [Matrix.mul_apply] at this
    simpa [Matrix.one_apply] using this
  have e : ∀ x : I, ∀ m : L, star (V k.2 x k.1) * star (F m k.2) * (V k'.2 x k'.1 * F m k'.2) =
      (star (V k.2 x k.1) * V k'.2 x k'.1) * (star (F m k.2) * F m k'.2) := fun _ _ => by ring
  simp_rw [e, ← Finset.mul_sum, hF']
  rcases k with ⟨a, l⟩; rcases k' with ⟨a', l'⟩
  simp only
  by_cases hl : l = l'
  · subst hl
    have := congrFun (congrFun (hV l) a) a'
    rw [Matrix.mul_apply] at this
    simp only [conjTranspose_apply] at this
    simp only [if_true, mul_one, this]
    simp [Matrix.one_apply]
  · simp only [hl, if_false, mul_zero, Finset.sum_const_zero]
    rw [Matrix.one_apply, if_neg]
    intro h; exact hl (congrArg Prod.snd h)

theorem x8_flag_decomp {I L : Type} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
    (w : L → ℝ) (tau : L → Matrix I I ℂ) (F : Matrix.unitaryGroup L ℂ)
    (V : L → Matrix I I ℂ) (lam : L → I → ℝ)
    (hτ : ∀ l, tau l = V l * diagonal (fun k => (lam l k : ℂ)) * (V l)ᴴ) :
    QAlgorithms.Papers.Independent.Gap48.P19.orthonormalFlagMixture w tau F =
      x8W V (F : Matrix L L ℂ) * diagonal (fun k => ((w k.2 * lam k.2 k.1 : ℝ) : ℂ)) *
        (x8W V (F : Matrix L L ℂ))ᴴ := by
  ext x y
  simp only [QAlgorithms.Papers.Independent.Gap48.P19.orthonormalFlagMixture, hτ]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply, x8W, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [Matrix.mul_apply, diagonal_apply, conjTranspose_apply, Finset.mul_sum,
    Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [star_mul', RCLike.star_def]
  push_cast
  ring

/-- entropy of a flag mixture -/
theorem x8_flag_ent {I L : Type} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
    (w : L → ℝ) (tau : L → Matrix I I ℂ) (F : Matrix.unitaryGroup L ℂ)
    (V : L → Matrix I I ℂ) (hV : ∀ l, (V l)ᴴ * V l = 1) (lam : L → I → ℝ)
    (hlam : ∀ l, ∑ k, lam l k = 1)
    (hτ : ∀ l, tau l = V l * diagonal (fun k => (lam l k : ℂ)) * (V l)ᴴ) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy
      (QAlgorithms.Papers.Independent.Gap48.P19.orthonormalFlagMixture w tau F) =
      -∑ l, w l * Real.log (w l) - ∑ l, w l * ∑ k, lam l k * Real.log (lam l k) := by
  have hF : (F : Matrix L L ℂ)ᴴ * F = 1 := Unitary.coe_star_mul_self F
  rw [x8_ent _ _ (x8_W1 V hV _ hF) _ (x8_flag_decomp w tau F V lam hτ)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [x8_flog, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hlam, one_mul]
  ring

end X8P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_kron_decomp {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ra : Mat A) (rb : Mat B) (ha : ra.IsHermitian) (hb : rb.IsHermitian) :
    Matrix.kronecker ra rb =
      Matrix.kronecker (ha.eigenvectorUnitary : Matrix A A ℂ) (hb.eigenvectorUnitary : Matrix B B ℂ) *
      diagonal (fun k : A × B => ((ha.eigenvalues k.1 * hb.eigenvalues k.2 : ℝ) : ℂ)) *
      (Matrix.kronecker (ha.eigenvectorUnitary : Matrix A A ℂ) (hb.eigenvectorUnitary : Matrix B B ℂ))ᴴ := by
  have e : diagonal (fun k : A × B => ((ha.eigenvalues k.1 * hb.eigenvalues k.2 : ℝ) : ℂ)) =
      Matrix.kronecker (diagonal (fun k => ((ha.eigenvalues k : ℝ) : ℂ)))
        (diagonal (fun k => ((hb.eigenvalues k : ℝ) : ℂ))) := by
    rw [show Matrix.kronecker (diagonal (fun k => ((ha.eigenvalues k : ℝ) : ℂ)))
        (diagonal (fun k => ((hb.eigenvalues k : ℝ) : ℂ))) =
        Matrix.kroneckerMap (· * ·) (diagonal (fun k => ((ha.eigenvalues k : ℝ) : ℂ)))
        (diagonal (fun k => ((hb.eigenvalues k : ℝ) : ℂ))) from rfl, Matrix.diagonal_kronecker_diagonal]
    congr 1; ext k; push_cast; rfl
  rw [e]
  conv_lhs => rw [X8P19.x8_spec ha, X8P19.x8_spec hb]
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

theorem x8_kron_unit {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Matrix A A ℂ) (V : Matrix B B ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (Matrix.kronecker U V)ᴴ * Matrix.kronecker U V = 1 := by
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV,
    Matrix.one_kronecker_one]

theorem x8_main {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    [DecidableEq A] [DecidableEq B] [DecidableEq L]
    [Nonempty A] [Nonempty B] [Nonempty L]
    (w : L → ℝ) (ra : L → Mat A) (rb : L → Mat B)
    (F : Matrix.unitaryGroup L ℂ) (hw : IsLaw w)
    (ha : ∀ l, IsDensityMatrix (ra l)) (hb : ∀ l, IsDensityMatrix (rb l)) :
    IsDensityMatrix (flaggedProduct w ra rb F) ∧
    extensionQuantumCMI (flaggedProduct w ra rb F) = 0 := by
  have hah : ∀ l, (ra l).IsHermitian := fun l => (ha l).1.1
  have hbh : ∀ l, (rb l).IsHermitian := fun l => (hb l).1.1
  set Va : L → Matrix A A ℂ := fun l => ((hah l).eigenvectorUnitary : Matrix A A ℂ)
  set Vb : L → Matrix B B ℂ := fun l => ((hbh l).eigenvectorUnitary : Matrix B B ℂ)
  set α : L → A → ℝ := fun l => (hah l).eigenvalues
  set β : L → B → ℝ := fun l => (hbh l).eigenvalues
  have hVa : ∀ l, (Va l)ᴴ * Va l = 1 := fun l => X8P19.x8_U1 (hah l)
  have hVb : ∀ l, (Vb l)ᴴ * Vb l = 1 := fun l => X8P19.x8_U1 (hbh l)
  have hα : ∀ l, ∑ k, α l k = 1 := fun l => X8P19.x8_sum_eig (hah l) (ha l).2
  have hβ : ∀ l, ∑ k, β l k = 1 := fun l => X8P19.x8_sum_eig (hbh l) (hb l).2
  have hα0 : ∀ l k, 0 ≤ α l k := fun l k => (ha l).1.eigenvalues_nonneg k
  have hβ0 : ∀ l k, 0 ≤ β l k := fun l k => (hb l).1.eigenvalues_nonneg k
  set V : L → Matrix (A × B) (A × B) ℂ := fun l => Matrix.kronecker (Va l) (Vb l)
  set γ : L → A × B → ℝ := fun l k => α l k.1 * β l k.2
  have hV : ∀ l, (V l)ᴴ * V l = 1 := fun l => x8_kron_unit _ _ (hVa l) (hVb l)
  have hγ : ∀ l, ∑ k, γ l k = 1 := fun l => by
    simp only [γ, Fintype.sum_prod_type, ← Finset.mul_sum, hβ, mul_one, hα]
  have hτ : ∀ l, Matrix.kronecker (ra l) (rb l) = V l * diagonal (fun k => (γ l k : ℂ)) * (V l)ᴴ :=
    fun l => x8_kron_decomp (ra l) (rb l) (hah l) (hbh l)
  have hτa : ∀ l, ra l = Va l * diagonal (fun k => (α l k : ℂ)) * (Va l)ᴴ := fun l => X8P19.x8_spec (hah l)
  have hτb : ∀ l, rb l = Vb l * diagonal (fun k => (β l k : ℂ)) * (Vb l)ᴴ := fun l => X8P19.x8_spec (hbh l)
  have hF : (F : Matrix L L ℂ)ᴴ * F = 1 := Unitary.coe_star_mul_self F
  have hdec := X8P19.x8_flag_decomp w (fun l => Matrix.kronecker (ra l) (rb l)) F V γ hτ
  have htra : ∀ l, ∑ a, ra l a a = 1 := fun l => (ha l).2
  have htrb : ∀ l, ∑ b, rb l b b = 1 := fun l => (hb l).2
  constructor
  · -- density
    unfold flaggedProduct
    rw [hdec]
    set W := X8P19.x8W V (F : Matrix L L ℂ)
    constructor
    · have hD : (diagonal (fun k : (A × B) × L => ((w k.2 * γ k.2 k.1 : ℝ) : ℂ))).PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro k
        exact Complex.zero_le_real.2 (mul_nonneg (hw.1 _) (mul_nonneg (hα0 _ _) (hβ0 _ _)))
      have := hD.conjTranspose_mul_mul_same Wᴴ
      rwa [conjTranspose_conjTranspose] at this
    · rw [Matrix.trace_mul_cycle, X8P19.x8_W1 V hV _ hF, Matrix.one_mul, trace_diagonal]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Complex.ofReal_mul, ← Finset.mul_sum]
      rw [← Complex.ofReal_one, ← hw.2]
      push_cast
      refine Finset.sum_congr rfl (fun l _ => ?_)
      have := hγ l
      rw [← Complex.ofReal_inj] at this
      push_cast at this
      rw [this, mul_one]
  · -- CMI
    have hAL : marginalAL (flaggedProduct w ra rb F) = orthonormalFlagMixture w ra F := by
      ext x y
      simp only [marginalAL, flaggedProduct, orthonormalFlagMixture, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      have e : ∀ b, (w l : ℂ) * (ra l x.1 y.1 * rb l b b) * (F : Matrix L L ℂ) x.2 l *
          conj ((F : Matrix L L ℂ) y.2 l) = ((w l : ℂ) * ra l x.1 y.1 * (F : Matrix L L ℂ) x.2 l *
          conj ((F : Matrix L L ℂ) y.2 l)) * rb l b b := fun b => by ring
      simp only [e, ← Finset.mul_sum, htrb, mul_one]
    have hBL : marginalBL (flaggedProduct w ra rb F) = orthonormalFlagMixture w rb F := by
      ext x y
      simp only [marginalBL, flaggedProduct, orthonormalFlagMixture, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      have e : ∀ a, (w l : ℂ) * (ra l a a * rb l x.1 y.1) * (F : Matrix L L ℂ) x.2 l *
          conj ((F : Matrix L L ℂ) y.2 l) = ((w l : ℂ) * rb l x.1 y.1 * (F : Matrix L L ℂ) x.2 l *
          conj ((F : Matrix L L ℂ) y.2 l)) * ra l a a := fun a => by ring
      simp only [e, ← Finset.mul_sum, htra, mul_one]
    have hL : traceLeft (flaggedProduct w ra rb F) =
        (F : Matrix L L ℂ) * diagonal (fun l => (w l : ℂ)) * (F : Matrix L L ℂ)ᴴ := by
      ext x y
      simp only [traceLeft, flaggedProduct, orthonormalFlagMixture, Matrix.kronecker,
        Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.mul_apply, diagonal_apply,
        conjTranspose_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      have e : ∀ a b, (w l : ℂ) * (ra l a a * rb l b b) * (F : Matrix L L ℂ) x l *
          conj ((F : Matrix L L ℂ) y l) = ((w l : ℂ) * (F : Matrix L L ℂ) x l *
          conj ((F : Matrix L L ℂ) y l)) * (ra l a a * rb l b b) := fun a b => by ring
      simp only [e, ← Finset.mul_sum, ← Finset.sum_mul, htra, htrb, mul_one, one_mul,
        RCLike.star_def]
      ring
    unfold extensionQuantumCMI
    rw [hAL, hBL, hL]
    rw [X8P19.x8_flag_ent w ra F Va hVa α hα hτa, X8P19.x8_flag_ent w rb F Vb hVb β hβ hτb,
      X8P19.x8_ent _ _ hF w rfl]
    unfold flaggedProduct
    rw [X8P19.x8_flag_ent w _ F V hV γ hγ hτ]
    have hγe : ∀ l, ∑ k, γ l k * Real.log (γ l k) =
        ∑ a, α l a * Real.log (α l a) + ∑ b, β l b * Real.log (β l b) := by
      intro l
      simp only [γ, Fintype.sum_prod_type, X8P19.x8_flog, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hα, hβ, one_mul]
      ring
    simp only [hγe, mul_add, Finset.sum_add_distrib]
    ring

end

end QAlgorithms.Papers.Independent.Gap48.P19

open QAlgorithms.Papers.Independent.Gap48.P19 in
open QAlgorithms.Papers.Independent.Information100.P75 (Mat) in
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw) in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    [DecidableEq A] [DecidableEq B] [DecidableEq L]
    [Nonempty A] [Nonempty B] [Nonempty L]
    (w : L → ℝ) (ra : L → Mat A) (rb : L → Mat B)
    (F : Matrix.unitaryGroup L ℂ) (hw : IsLaw w)
    (ha : ∀ l, QAlgorithms.IsDensityMatrix (ra l)) (hb : ∀ l, QAlgorithms.IsDensityMatrix (rb l)) :
    QAlgorithms.IsDensityMatrix (flaggedProduct w ra rb F) ∧
    extensionQuantumCMI (flaggedProduct w ra rb F) = 0 :=
  x8_main w ra rb F hw ha hb
