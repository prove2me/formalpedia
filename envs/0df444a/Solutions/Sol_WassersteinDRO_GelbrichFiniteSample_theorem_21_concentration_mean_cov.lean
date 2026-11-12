-- Prove2me | solution 1 for WassersteinDRO.GelbrichFiniteSample.theorem_21_concentration_mean_cov
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T20:01:43.61696+00:00
-- url     : https://prove2.me/submissions/4babb43d-02fd-4408-aad7-0b7086a047d6

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleMean
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_uncertaintySet

set_option autoImplicit false

open MeasureTheory Matrix
open scoped MatrixOrder

namespace G21Aux

/-- Cauchy-Schwarz in the form used for the trace inequality. -/
lemma dot_le_of_sq {m : ℕ} (x y : Fin m → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = s ^ 2) : x ⬝ᵥ y ≤ s := by
  have key : ∀ t : ℝ, 0 ≤ t ^ 2 * (x ⬝ᵥ x) - 2 * t * (x ⬝ᵥ y) + y ⬝ᵥ y := by
    intro t
    have h0 : 0 ≤ ∑ i, (t * x i - y i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h1 : ∑ i, (t * x i - y i) ^ 2
        = t ^ 2 * (x ⬝ᵥ x) - 2 * t * (x ⬝ᵥ y) + y ⬝ᵥ y := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    linarith
  have h2 := key (x ⬝ᵥ y)
  rw [hx, hy] at h2
  nlinarith [sq_nonneg (x ⬝ᵥ y - s), sq_nonneg (x ⬝ᵥ y + s)]

/-- `tr W ≤ tr M` whenever `M` is positive semidefinite and `M * M = Wᵀ * W`
(the trace of `W` is at most the trace of its modulus). -/
lemma trace_le_of_mul_self {m : ℕ} (W M : Matrix (Fin m) (Fin m) ℝ) (hM : M.PosSemidef)
    (h : M * M = Wᵀ * W) : W.trace ≤ M.trace := by
  classical
  have hH := hM.1
  let U : Matrix (Fin m) (Fin m) ℝ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  have hUU : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose] using this
  have hUU' : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose] using this
  let v : Fin m → (Fin m → ℝ) := fun k => ⇑(hH.eigenvectorBasis k)
  have hUv : ∀ i k, U i k = v k i := fun i k => rfl
  have htr : ∀ X : Matrix (Fin m) (Fin m) ℝ, X.trace = ∑ k, v k ⬝ᵥ (X *ᵥ v k) := by
    intro X
    have e1 : X.trace = (Uᵀ * X * U).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [e1]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
      Matrix.mulVec, hUv, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hvv : ∀ k, v k ⬝ᵥ v k = 1 := by
    intro k
    have := congrFun (congrFun hUU k) k
    simpa [Matrix.mul_apply, dotProduct, hUv] using this
  have hMv : ∀ k, M *ᵥ v k = hH.eigenvalues k • v k := fun k => hH.mulVec_eigenvectorBasis k
  rw [htr W, htr M]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hl := hM.eigenvalues_nonneg k
  have e2 : v k ⬝ᵥ (M *ᵥ v k) = hH.eigenvalues k := by
    rw [hMv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
  rw [e2]
  apply dot_le_of_sq _ _ _ hl (hvv k)
  have e3 : (W *ᵥ v k) ⬝ᵥ (W *ᵥ v k) = v k ⬝ᵥ ((Wᵀ * W) *ᵥ v k) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (v k), Matrix.vecMul_transpose]
  rw [e3, ← h, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, hMv, smul_smul, dotProduct_smul,
    hvv, smul_eq_mul, mul_one, sq]

lemma trace_sqrt_nonneg {m : ℕ} (X : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ (CFC.sqrt X).trace := by
  have : 0 ≤ CFC.sqrt X := CFC.sqrt_nonneg X
  exact (Matrix.nonneg_iff_posSemidef.mp this).trace_nonneg

/-- The Bures term is at most the squared Frobenius distance of the square roots. -/
lemma bures_le_sqrt_dist {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    (A + B - 2 • CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)).trace
      ≤ ((CFC.sqrt A - CFC.sqrt B) * (CFC.sqrt A - CFC.sqrt B)).trace := by
  have hA0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hB0 : 0 ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
  set a := CFC.sqrt A with ha
  set b := CFC.sqrt B with hb
  have ha0 : 0 ≤ a := CFC.sqrt_nonneg A
  have hb0 : 0 ≤ b := CFC.sqrt_nonneg B
  have haP : a.PosSemidef := Matrix.nonneg_iff_posSemidef.mp ha0
  have hbP : b.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hb0
  have haT : aᵀ = a := by simpa using haP.1.eq
  have hbT : bᵀ = b := by simpa using hbP.1.eq
  have haa : a * a = A := CFC.sqrt_mul_sqrt_self A hA0
  have hbb : b * b = B := CFC.sqrt_mul_sqrt_self B hB0
  have hX : (a * B * a).PosSemidef := by
    have := hB.conjTranspose_mul_mul_same a
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, haT] using this
  have hX0 : 0 ≤ a * B * a := Matrix.nonneg_iff_posSemidef.mpr hX
  set M := CFC.sqrt (a * B * a) with hMdef
  have hM0 : 0 ≤ M := CFC.sqrt_nonneg _
  have hMP : M.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hM0
  have hMM : M * M = (b * a)ᵀ * (b * a) := by
    rw [CFC.sqrt_mul_sqrt_self _ hX0, Matrix.transpose_mul, haT, hbT, ← hbb]
    simp only [Matrix.mul_assoc]
  have key := trace_le_of_mul_self (b * a) M hMP hMM
  have hab : (a * b).trace = (b * a).trace := Matrix.trace_mul_comm a b
  have e : ((a - b) * (a - b)).trace = A.trace + B.trace - 2 * (b * a).trace := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, haa, hbb]
    simp only [Matrix.trace_sub]
    linarith
  rw [e, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, nsmul_eq_mul, Nat.cast_ofNat]
  linarith

lemma sym_dot {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : Sᵀ = S) (x y : Fin m → ℝ) :
    x ⬝ᵥ (S *ᵥ y) = (S *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]

lemma cfc_mulVec_eig {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ)
    (i : Fin m) :
    cfc f A *ᵥ ⇑(hA.eigenvectorBasis i) = f (hA.eigenvalues i) • ⇑(hA.eigenvectorBasis i) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec,
    hA.star_eigenvectorUnitary_mulVec i, ← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single]
  have : (Pi.single i ((RCLike.ofReal ∘ f ∘ hA.eigenvalues) i * 1) : Fin m → ℝ)
      = f (hA.eigenvalues i) • Pi.single i 1 := by
    ext j; simp [Pi.single_apply]
  rw [this, Matrix.mulVec_smul, hA.eigenvectorUnitary_mulVec i]

lemma sqrt_mulVec_eig {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (i : Fin m) :
    CFC.sqrt A *ᵥ ⇑(hA.1.eigenvectorBasis i)
      = Real.sqrt (hA.1.eigenvalues i) • ⇑(hA.1.eigenvectorBasis i) := by
  have hA0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  rw [CFC.sqrt_eq_real_sqrt A hA0, cfcₙ_eq_cfc]
  exact cfc_mulVec_eig A hA.1 Real.sqrt i

lemma frob_eq {m : ℕ} (X P Q : Matrix (Fin m) (Fin m) ℝ) (hP : P * Pᵀ = 1) (hQ : Q * Qᵀ = 1) :
    (Xᵀ * X).trace = ∑ i, ∑ j, ((fun k => P k i) ⬝ᵥ (X *ᵥ fun k => Q k j)) ^ 2 := by
  have h1 : ∀ Y : Matrix (Fin m) (Fin m) ℝ, (Yᵀ * Y).trace = ∑ i, ∑ j, Y i j ^ 2 := by
    intro Y
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
    rw [Finset.sum_comm]
  have h2 : (Xᵀ * X).trace = ((Pᵀ * X * Q)ᵀ * (Pᵀ * X * Q)).trace := by
    rw [show (Pᵀ * X * Q)ᵀ * (Pᵀ * X * Q) = Qᵀ * (Xᵀ * X * Q) from by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P, hP, Matrix.one_mul]]
    rw [Matrix.trace_mul_comm Qᵀ, Matrix.mul_assoc, Matrix.mul_assoc, hQ, Matrix.mul_one]
  rw [h2, h1]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))

/-- Square-root perturbation bound: with `ker B ⊆ ker A` and every eigenvalue of `B` either
`0` or at least `lam > 0`, `lam * ‖√A - √B‖_F² ≤ ‖A - B‖_F²`. -/
lemma sqrt_dist_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (lam : ℝ) (hlam : 0 < lam)
    (hker : ∀ x, B *ᵥ x = 0 → A *ᵥ x = 0)
    (hgap : ∀ j, hB.1.eigenvalues j = 0 ∨ lam ≤ hB.1.eigenvalues j) :
    lam * ((CFC.sqrt A - CFC.sqrt B) * (CFC.sqrt A - CFC.sqrt B)).trace
      ≤ ((A - B)ᵀ * (A - B)).trace := by
  classical
  let p : Fin m → Fin m → ℝ := fun i => ⇑(hA.1.eigenvectorBasis i)
  let q : Fin m → Fin m → ℝ := fun j => ⇑(hB.1.eigenvectorBasis j)
  let P : Matrix (Fin m) (Fin m) ℝ := (hA.1.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  let Q : Matrix (Fin m) (Fin m) ℝ := (hB.1.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  have hP : P * Pᵀ = 1 := by
    have := Unitary.coe_mul_star_self hA.1.eigenvectorUnitary
    simpa [P, Matrix.star_eq_conjTranspose] using this
  have hQ : Q * Qᵀ = 1 := by
    have := Unitary.coe_mul_star_self hB.1.eigenvectorUnitary
    simpa [Q, Matrix.star_eq_conjTranspose] using this
  have hAT : Aᵀ = A := by simpa using hA.1.eq
  have hBT : Bᵀ = B := by simpa using hB.1.eq
  have haP : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hbP : (CFC.sqrt B).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have haT : (CFC.sqrt A)ᵀ = CFC.sqrt A := by simpa using haP.1.eq
  have hbT : (CFC.sqrt B)ᵀ = CFC.sqrt B := by simpa using hbP.1.eq
  have hDT : (CFC.sqrt A - CFC.sqrt B)ᵀ = CFC.sqrt A - CFC.sqrt B := by
    rw [Matrix.transpose_sub, haT, hbT]
  rw [show (CFC.sqrt A - CFC.sqrt B) * (CFC.sqrt A - CFC.sqrt B)
      = (CFC.sqrt A - CFC.sqrt B)ᵀ * (CFC.sqrt A - CFC.sqrt B) by rw [hDT],
    frob_eq _ P Q hP hQ, frob_eq _ P Q hP hQ, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  change lam * (p i ⬝ᵥ ((CFC.sqrt A - CFC.sqrt B) *ᵥ q j)) ^ 2 ≤ (p i ⬝ᵥ ((A - B) *ᵥ q j)) ^ 2
  have hsa := sqrt_mulVec_eig A hA i
  have hsb := sqrt_mulVec_eig B hB j
  have hAp : A *ᵥ p i = hA.1.eigenvalues i • p i := hA.1.mulVec_eigenvectorBasis i
  have hBq : B *ᵥ q j = hB.1.eigenvalues j • q j := hB.1.mulVec_eigenvectorBasis j
  set α := hA.1.eigenvalues i with hαdef
  set β := hB.1.eigenvalues j with hβdef
  have hα0 : 0 ≤ α := hA.eigenvalues_nonneg i
  have hβ0 : 0 ≤ β := hB.eigenvalues_nonneg j
  set x := p i ⬝ᵥ q j with hx
  have e1 : p i ⬝ᵥ ((CFC.sqrt A - CFC.sqrt B) *ᵥ q j) = (Real.sqrt α - Real.sqrt β) * x := by
    rw [Matrix.sub_mulVec, dotProduct_sub, sym_dot (CFC.sqrt A) haT]
    change (CFC.sqrt A *ᵥ p i) ⬝ᵥ q j - p i ⬝ᵥ (CFC.sqrt B *ᵥ q j) = _
    rw [hsa, hsb, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have e2 : p i ⬝ᵥ ((A - B) *ᵥ q j) = (α - β) * x := by
    rw [Matrix.sub_mulVec, dotProduct_sub, sym_dot A hAT, hAp, hBq, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [e1, e2]
  rcases hgap j with h0 | hl
  · replace h0 : β = 0 := h0
    have hBq0 : B *ᵥ q j = 0 := by rw [hBq, h0, zero_smul]
    have hAq0 := hker _ hBq0
    have hax : α * x = 0 := by
      have h3 : p i ⬝ᵥ (A *ᵥ q j) = 0 := by rw [hAq0, dotProduct_zero]
      rw [sym_dot A hAT, hAp, smul_dotProduct, smul_eq_mul] at h3
      exact h3
    rw [h0, Real.sqrt_zero, sub_zero, sub_zero]
    have h4 : (Real.sqrt α * x) ^ 2 = (α * x) * x := by
      rw [mul_pow, Real.sq_sqrt hα0]; ring
    rw [h4, hax]
    simp
  · replace hl : lam ≤ β := hl
    have hsa0 := Real.sqrt_nonneg α
    have hsb0 := Real.sqrt_nonneg β
    have hα2 := Real.sq_sqrt hα0
    have hβ2 := Real.sq_sqrt hβ0
    have hfac : α - β = (Real.sqrt α - Real.sqrt β) * (Real.sqrt α + Real.sqrt β) := by
      nlinarith
    have hs : lam ≤ (Real.sqrt α + Real.sqrt β) ^ 2 := by nlinarith [mul_nonneg hsa0 hsb0]
    rw [hfac]
    calc lam * ((Real.sqrt α - Real.sqrt β) * x) ^ 2
        ≤ (Real.sqrt α + Real.sqrt β) ^ 2 * ((Real.sqrt α - Real.sqrt β) * x) ^ 2 :=
          mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = ((Real.sqrt α - Real.sqrt β) * (Real.sqrt α + Real.sqrt β) * x) ^ 2 := by ring


/-! ### Probability part (session 2) -/

lemma exp_le_quad (x : ℝ) : Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have he : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  have hx2 : x ^ 2 ≤ x ^ 2 * Real.exp |x| := le_mul_of_one_le_right (sq_nonneg x) he
  rcases le_or_gt |x| 1 with h | h
  · have h1 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h)).2
    linarith
  · rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h he hx2 ⊢
      have h1 : 1 ≤ x ^ 2 := by nlinarith
      have h2 : Real.exp x ≤ x ^ 2 * Real.exp x := le_mul_of_one_le_left (Real.exp_pos x).le h1
      linarith
    · have hx1 : x < -1 := by rw [abs_of_neg hx] at h; linarith
      have h3 : Real.exp x ≤ 1 := by simpa using Real.exp_le_exp.mpr hx.le
      nlinarith

lemma sq_le_two_exp (x : ℝ) : x ^ 2 ≤ 2 * Real.exp |x| := by
  have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [abs_nonneg x]

lemma exp_mul_le (t τ y : ℝ) (ht : |t| ≤ τ) :
    Real.exp (t * y) ≤ 1 + t * y + 2 * t ^ 2 * Real.exp ((1 + τ) * |y|) := by
  have h1 := exp_le_quad (t * y)
  have h2 : (t * y) ^ 2 ≤ t ^ 2 * (2 * Real.exp |y|) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left (sq_le_two_exp y) (sq_nonneg t)
  have h3 : Real.exp |t * y| ≤ Real.exp (τ * |y|) := by
    rw [Real.exp_le_exp, abs_mul]; exact mul_le_mul_of_nonneg_right ht (abs_nonneg y)
  have h4 : Real.exp ((1 + τ) * |y|) = Real.exp |y| * Real.exp (τ * |y|) := by
    rw [← Real.exp_add]; ring_nf
  have h5 : (t * y) ^ 2 * Real.exp |t * y| ≤ t ^ 2 * (2 * Real.exp |y|) * Real.exp (τ * |y|) :=
    mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
  rw [h4]
  have h6 : t ^ 2 * (2 * Real.exp |y|) * Real.exp (τ * |y|)
      = 2 * t ^ 2 * (Real.exp |y| * Real.exp (τ * |y|)) := by ring
  linarith

lemma mgf_le {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (f : E → ℝ) (hfm : Measurable f) (τ : ℝ)
    (hint : Integrable (fun x => Real.exp ((1 + τ) * |f x|)) P) (h0 : ∫ x, f x ∂P = 0)
    (t : ℝ) (ht : |t| ≤ τ) :
    Integrable (fun x => Real.exp (t * f x)) P ∧
    ∫ x, Real.exp (t * f x) ∂P ≤ 1 + 2 * t ^ 2 * ∫ x, Real.exp ((1 + τ) * |f x|) ∂P := by
  have hτ : 0 ≤ τ := le_trans (abs_nonneg t) ht
  have hfi : Integrable f P := by
    refine hint.mono' hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    have h1 := Real.add_one_le_exp ((1 + τ) * |f x|)
    have h2 : |f x| ≤ (1 + τ) * |f x| := le_mul_of_one_le_left (abs_nonneg _) (by linarith)
    linarith
  have hei : Integrable (fun x => Real.exp (t * f x)) P := by
    refine hint.mono' (Measurable.exp (hfm.const_mul t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    calc t * f x ≤ |t| * |f x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ (1 + τ) * |f x| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  refine ⟨hei, ?_⟩
  have hA : Integrable (fun x => 1 + t * f x) P := (integrable_const 1).add (hfi.const_mul t)
  have hrhs : Integrable (fun x => 1 + t * f x + 2 * t ^ 2 * Real.exp ((1 + τ) * |f x|)) P :=
    hA.add (hint.const_mul (2 * t ^ 2))
  calc ∫ x, Real.exp (t * f x) ∂P
      ≤ ∫ x, (1 + t * f x + 2 * t ^ 2 * Real.exp ((1 + τ) * |f x|)) ∂P :=
        integral_mono hei hrhs (fun x => exp_mul_le t τ (f x) ht)
    _ = 1 + 2 * t ^ 2 * ∫ x, Real.exp ((1 + τ) * |f x|) ∂P := by
        rw [integral_add hA (hint.const_mul _), integral_add (integrable_const 1) (hfi.const_mul t),
          integral_const_mul, integral_const_mul, h0]
        simp

/-- Chernoff bound for an i.i.d. sum under the product measure. -/
lemma chernoff_pi {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (f : E → ℝ) (hfm : Measurable f) (κ : ℝ) (hκ : 0 < κ) (K : ℝ)
    (hint : Integrable (fun x => Real.exp ((1 + κ⁻¹) * |f x|)) P)
    (hK : ∫ x, Real.exp ((1 + κ⁻¹) * |f x|) ∂P ≤ K) (h0 : ∫ x, f x ∂P = 0)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) :
    Measure.pi (fun _ : Fin N => P) {x | κ * ε * N ≤ ∑ i, f (x i)}
      ≤ ENNReal.ofReal (Real.exp (2 * K / κ ^ 2 - ε * Real.sqrt N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hsN1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hNsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hNr.le).symm
  set t : ℝ := κ⁻¹ * (Real.sqrt N)⁻¹ with htdef
  have ht0 : 0 ≤ t := by positivity
  have htτ : |t| ≤ κ⁻¹ := by
    rw [abs_of_nonneg ht0, htdef]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hκ.le) (inv_le_one_of_one_le₀ hsN1)
  obtain ⟨hei, hmgf⟩ := mgf_le P f hfm κ⁻¹ hint h0 t htτ
  set Q := Measure.pi (fun _ : Fin N => P) with hQ
  set I := ∫ x, Real.exp (t * f x) ∂P with hI
  have hI0 : 0 ≤ I := integral_nonneg (fun x => (Real.exp_pos _).le)
  have hIle : I ≤ Real.exp (2 * t ^ 2 * K) := by
    have h1 : I ≤ 1 + 2 * t ^ 2 * K := by
      have := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ 2 * t ^ 2)
      linarith
    have h2 := Real.add_one_le_exp (2 * t ^ 2 * K)
    linarith
  have hts : t * (κ * ε * N) = ε * Real.sqrt N := by
    rw [htdef]
    generalize Real.sqrt (N : ℝ) = s at hsN hNsq ⊢
    rw [hNsq]
    calc κ⁻¹ * s⁻¹ * (κ * ε * (s * s)) = (κ⁻¹ * κ) * (s⁻¹ * s) * (ε * s) := by ring
      _ = ε * s := by rw [inv_mul_cancel₀ hκ.ne', inv_mul_cancel₀ hsN.ne']; ring
  have hNt : (N : ℝ) * (2 * t ^ 2 * K) = 2 * K / κ ^ 2 := by
    rw [htdef]
    generalize Real.sqrt (N : ℝ) = s at hsN hNsq ⊢
    rw [hNsq]
    calc s * s * (2 * (κ⁻¹ * s⁻¹) ^ 2 * K) = 2 * K * κ⁻¹ ^ 2 * (s⁻¹ * s) ^ 2 := by ring
      _ = 2 * K / κ ^ 2 := by rw [inv_mul_cancel₀ hsN.ne']; ring
  set g : (Fin N → E) → ℝ := fun x => ∏ i, Real.exp (t * f (x i)) with hg
  have hgi : Integrable g Q := Integrable.fintype_prod (fun _ => hei)
  have hg0 : 0 ≤ᵐ[Q] g := Filter.Eventually.of_forall
    (fun x => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))
  have hsub : {x : Fin N → E | κ * ε * N ≤ ∑ i, f (x i)} ⊆
      {x | ENNReal.ofReal (Real.exp (t * (κ * ε * N))) ≤ ENNReal.ofReal (g x)} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    apply ENNReal.ofReal_le_ofReal
    simp only [hg]
    rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hx ht0
  have hM := mul_meas_ge_le_lintegral₀ hgi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal (Real.exp (t * (κ * ε * N))))
  have hlin : ∫⁻ x, ENNReal.ofReal (g x) ∂Q ≤ ENNReal.ofReal (Real.exp (2 * K / κ ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi hg0]
    apply ENNReal.ofReal_le_ofReal
    have e1 : ∫ x, g x ∂Q = I ^ N := by
      simp only [hg, hQ, hI]
      exact (integral_fintype_prod_eq_pow (ι := Fin N) (fun x => Real.exp (t * f x)) (μ := P)).trans
        (by rw [Fintype.card_fin])
    rw [e1, ← hNt, Real.exp_nat_mul]
    exact pow_le_pow_left₀ hI0 hIle N
  have key := hM.trans hlin
  calc Q {x | κ * ε * N ≤ ∑ i, f (x i)}
      ≤ Q {x | ENNReal.ofReal (Real.exp (t * (κ * ε * N))) ≤ ENNReal.ofReal (g x)} :=
        measure_mono hsub
    _ = ENNReal.ofReal (Real.exp (-(t * (κ * ε * N)))) *
          (ENNReal.ofReal (Real.exp (t * (κ * ε * N))) *
            Q {x | ENNReal.ofReal (Real.exp (t * (κ * ε * N))) ≤ ENNReal.ofReal (g x)}) := by
        rw [← mul_assoc (ENNReal.ofReal _), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(t * (κ * ε * N)))) *
          ENNReal.ofReal (Real.exp (2 * K / κ ^ 2)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (2 * K / κ ^ 2 - ε * Real.sqrt N)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hts]
        ring_nf

/-- Exponential-square moments from the `exp ‖ξ‖^α` moment, uniformly in `P`. -/
lemma moment_bound {m : ℕ} (α A D : ℝ) (hα : 2 < α) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ K : ℝ, ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P],
      ∫⁻ ξ, ENNReal.ofReal (Real.exp (‖ξ‖ ^ α)) ∂P ≤ ENNReal.ofReal A →
      Integrable (fun ξ => Real.exp (D * (1 + ‖ξ‖ ^ 2))) P ∧
      ∫ ξ, Real.exp (D * (1 + ‖ξ‖ ^ 2)) ∂P ≤ K := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < α - 2 by linarith)).eventually_ge_atTop (2 * D))
  set R' := max R 1 with hR'
  refine ⟨Real.exp (D * (1 + R' ^ 2)) + A, fun P _ hP => ?_⟩
  have hpt : ∀ ξ : EuclideanSpace ℝ (Fin m),
      Real.exp (D * (1 + ‖ξ‖ ^ 2)) ≤ Real.exp (D * (1 + R' ^ 2)) + Real.exp (‖ξ‖ ^ α) := by
    intro ξ
    rcases le_or_gt ‖ξ‖ R' with h | h
    · have h1 : ‖ξ‖ ^ 2 ≤ R' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      have h2 : Real.exp (D * (1 + ‖ξ‖ ^ 2)) ≤ Real.exp (D * (1 + R' ^ 2)) := by
        rw [Real.exp_le_exp]; nlinarith
      linarith [Real.exp_pos (‖ξ‖ ^ α)]
    · have hr1 : 1 ≤ ‖ξ‖ := le_trans (le_max_right _ _) h.le
      have hrR : R ≤ ‖ξ‖ := le_trans (le_max_left _ _) h.le
      have h2 : 2 * D ≤ ‖ξ‖ ^ (α - 2) := hR _ hrR
      have hsplit : ‖ξ‖ ^ α = ‖ξ‖ ^ (2 : ℝ) * ‖ξ‖ ^ (α - 2) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf
      have hsq : ‖ξ‖ ^ (2 : ℝ) = ‖ξ‖ ^ 2 := Real.rpow_two _
      have h3 : D * (1 + ‖ξ‖ ^ 2) ≤ ‖ξ‖ ^ α := by
        rw [hsplit, hsq]
        have h4 : 1 ≤ ‖ξ‖ ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖ξ‖), mul_le_mul_of_nonneg_left h4 hD]
      linarith [Real.exp_le_exp.mpr h3, Real.exp_pos (D * (1 + R' ^ 2))]
  have hem : Measurable (fun ξ : EuclideanSpace ℝ (Fin m) => Real.exp (‖ξ‖ ^ α)) := by
    fun_prop
  have hei : Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => Real.exp (‖ξ‖ ^ α)) P := by
    refine ⟨hem.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hP ENNReal.ofReal_lt_top
  have hgi : Integrable (fun ξ => Real.exp (D * (1 + ‖ξ‖ ^ 2))) P := by
    refine ((integrable_const (Real.exp (D * (1 + R' ^ 2)))).add hei).mono'
      (by fun_prop) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpt ξ
  refine ⟨hgi, ?_⟩
  have hint_e : ∫ ξ, Real.exp (‖ξ‖ ^ α) ∂P ≤ A := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) hei.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hA hP
  calc ∫ ξ, Real.exp (D * (1 + ‖ξ‖ ^ 2)) ∂P
      ≤ ∫ ξ, (Real.exp (D * (1 + R' ^ 2)) + Real.exp (‖ξ‖ ^ α)) ∂P :=
        integral_mono hgi ((integrable_const _).add hei) hpt
    _ = Real.exp (D * (1 + R' ^ 2)) + ∫ ξ, Real.exp (‖ξ‖ ^ α) ∂P := by
        rw [integral_add (integrable_const _) hei]; simp
    _ ≤ Real.exp (D * (1 + R' ^ 2)) + A := by linarith

/-- On the support of a PSD matrix: if `y` is orthogonal to every null eigenvector of `S`,
then `y` is orthogonal to `ker S`. -/
lemma ker_orth {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef) (x y : Fin m → ℝ)
    (hx : S *ᵥ x = 0)
    (hy : ∀ j, hS.1.eigenvalues j = 0 → ⇑(hS.1.eigenvectorBasis j) ⬝ᵥ y = 0) :
    y ⬝ᵥ x = 0 := by
  classical
  let Q : Matrix (Fin m) (Fin m) ℝ := (hS.1.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  have hQ : Q * Qᵀ = 1 := by
    have := Unitary.coe_mul_star_self hS.1.eigenvectorUnitary
    simpa [Q, Matrix.star_eq_conjTranspose] using this
  have hST : Sᵀ = S := by simpa using hS.1.eq
  have e1 : y ⬝ᵥ x = (y ᵥ* Q) ⬝ᵥ (Qᵀ *ᵥ x) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  rw [e1]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have ea : (y ᵥ* Q) j = y ⬝ᵥ ⇑(hS.1.eigenvectorBasis j) := rfl
  have eb : (Qᵀ *ᵥ x) j = ⇑(hS.1.eigenvectorBasis j) ⬝ᵥ x := rfl
  rw [ea, eb]
  by_cases hj : hS.1.eigenvalues j = 0
  · rw [dotProduct_comm, hy j hj, zero_mul]
  · have h1 : ⇑(hS.1.eigenvectorBasis j) ⬝ᵥ (S *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
    rw [sym_dot S hST, hS.1.mulVec_eigenvectorBasis j, smul_dotProduct, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hj
    · rw [h, mul_zero]

lemma coord_sum {m N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    (∑ i, f i) j = ∑ i, f i j := by
  change (WithLp.ofLp (∑ i, f i)) j = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

lemma coord_integral {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m)))
    (hi : Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => ξ) P) (j : Fin m) :
    (∫ ξ, ξ ∂P) j = ∫ ξ, ξ j ∂P := by
  have := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin m => ℝ) j).integral_comp_comm hi
  simpa using this.symm

open WassersteinDRO.GelbrichFiniteSample in
lemma mean_coord {m N : ℕ} (hN : 0 < N) (ξh : Fin N → EuclideanSpace ℝ (Fin m))
    (μ : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    (sampleMean ξh - μ) j = (N : ℝ)⁻¹ * ∑ i, (ξh i j - μ j) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [PiLp.sub_apply, sampleMean, PiLp.smul_apply, coord_sum, smul_eq_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub, ← mul_assoc,
    inv_mul_cancel₀ hNr, one_mul]

open WassersteinDRO.GelbrichFiniteSample in
lemma sampleCov_eq {m N : ℕ} (hN : 0 < N) (ξh : Fin N → EuclideanSpace ℝ (Fin m))
    (μ : EuclideanSpace ℝ (Fin m)) (j k : Fin m) :
    sampleCov ξh j k = (N : ℝ)⁻¹ * ∑ i, (ξh i j - μ j) * (ξh i k - μ k)
      - (sampleMean ξh - μ) j * (sampleMean ξh - μ) k := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : ∀ i l, (ξh i - sampleMean ξh) l = (ξh i l - μ l) - (sampleMean ξh - μ) l := by
    intro i l; rw [PiLp.sub_apply, PiLp.sub_apply]; ring
  have hA' : ∑ i, (ξh i j - μ j) = N * (sampleMean ξh - μ) j := by
    rw [mean_coord hN, ← mul_assoc, mul_inv_cancel₀ hNr, one_mul]
  have hB' : ∑ i, (ξh i k - μ k) = N * (sampleMean ξh - μ) k := by
    rw [mean_coord hN, ← mul_assoc, mul_inv_cancel₀ hNr, one_mul]
  simp only [sampleCov, Matrix.of_apply, hs]
  set A := (sampleMean ξh - μ) j with hA
  set B := (sampleMean ξh - μ) k with hB
  have e : ∑ i, ((ξh i j - μ j) - A) * ((ξh i k - μ k) - B)
      = ∑ i, (ξh i j - μ j) * (ξh i k - μ k) - B * ∑ i, (ξh i j - μ j)
        - A * ∑ i, (ξh i k - μ k) + N * (A * B) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    rw [show (N : ℝ) * (A * B) = ∑ _i : Fin N, A * B by simp]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e, hA', hB']
  have h1 : (N : ℝ)⁻¹ * N = 1 := inv_mul_cancel₀ hNr
  linear_combination (-(A * B)) * h1

open WassersteinDRO.GelbrichFiniteSample in
lemma sampleCov_psd {m N : ℕ} (ξh : Fin N → EuclideanSpace ℝ (Fin m)) :
    (sampleCov ξh).PosSemidef := by
  have e : sampleCov ξh = ∑ i, (N : ℝ)⁻¹ • Matrix.vecMulVec (fun l => (ξh i - sampleMean ξh) l)
      (star fun l => (ξh i - sampleMean ξh) l) := by
    ext j k
    simp [sampleCov, Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.mul_sum]
  rw [e]
  exact Matrix.posSemidef_sum _ (fun i _ =>
    (Matrix.posSemidef_vecMulVec_self_star _).smul (inv_nonneg.mpr (Nat.cast_nonneg N)))

open WassersteinDRO.GelbrichFiniteSample in
/-- Deterministic core: on the good event the pair `(μ, Σ)` lies in `U_ε(μ̂, Σ̂)`. -/
lemma det_bound {m N : ℕ} (hN : 0 < N) (ξh : Fin N → EuclideanSpace ℝ (Fin m))
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) (hS : Sig.PosSemidef)
    (lam : ℝ) (hlam : 0 < lam) (hgap : ∀ j, hS.1.eigenvalues j = 0 ∨ lam ≤ hS.1.eigenvalues j)
    (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε)
    (hκ1 : κ * (1 + 2 * Sig.trace) ≤ 1) (hκm : κ * m ≤ 1)
    (hκ2 : κ ^ 2 * (m + 4 * m ^ 2 / lam) ≤ 1)
    (hd : ∀ j, |(N : ℝ)⁻¹ * ∑ i, (ξh i j - μ j)| ≤ κ * ε)
    (hW : ∀ j k, |(N : ℝ)⁻¹ * ∑ i, (ξh i j - μ j) * (ξh i k - μ k) - Sig j k| ≤ κ * ε)
    (hker : ∀ i j, hS.1.eigenvalues j = 0 →
      ⇑(hS.1.eigenvectorBasis j) ⬝ᵥ (fun k => ξh i k - μ k) = 0) :
    (μ, Sig) ∈ uncertaintySet ε (sampleMean ξh) (sampleCov ξh) := by
  refine ⟨hS, ?_⟩
  change ‖sampleMean ξh - μ‖ ^ 2 + (sampleCov ξh + Sig
      - 2 • CFC.sqrt (CFC.sqrt (sampleCov ξh) * Sig * CFC.sqrt (sampleCov ξh))).trace ≤ ε ^ 2
  have hSh : (sampleCov ξh).PosSemidef := sampleCov_psd ξh
  have hnorm : ‖sampleMean ξh - μ‖ ^ 2 = ∑ j, ((sampleMean ξh - μ) j) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq _
  have hdb : ∀ j, |(sampleMean ξh - μ) j| ≤ κ * ε := fun j => by rw [mean_coord hN]; exact hd j
  have hent : ∀ j k, sampleCov ξh j k - Sig j k
      = ((N : ℝ)⁻¹ * ∑ i, (ξh i j - μ j) * (ξh i k - μ k) - Sig j k)
        - (sampleMean ξh - μ) j * (sampleMean ξh - μ) k := by
    intro j k; rw [sampleCov_eq hN ξh μ]; ring
  have htrS : 0 ≤ Sig.trace := hS.trace_nonneg
  have hd2 : ∀ j, ((sampleMean ξh - μ) j) ^ 2 ≤ (κ * ε) ^ 2 := fun j => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdb j) 2
  have hdsum : ∑ j, ((sampleMean ξh - μ) j) ^ 2 ≤ m * (κ * ε) ^ 2 := by
    calc ∑ j, ((sampleMean ξh - μ) j) ^ 2 ≤ ∑ _j : Fin m, (κ * ε) ^ 2 :=
          Finset.sum_le_sum (fun j _ => hd2 j)
      _ = m * (κ * ε) ^ 2 := by simp
  rw [hnorm]
  by_cases hbig : 1 + 2 * Sig.trace ≤ ε
  · have hsq0 := trace_sqrt_nonneg (CFC.sqrt (sampleCov ξh) * Sig * CFC.sqrt (sampleCov ξh))
    have hT : (sampleCov ξh + Sig
        - 2 • CFC.sqrt (CFC.sqrt (sampleCov ξh) * Sig * CFC.sqrt (sampleCov ξh))).trace
        ≤ (sampleCov ξh).trace + Sig.trace := by
      rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, nsmul_eq_mul, Nat.cast_ofNat]
      linarith
    have htrSh : (sampleCov ξh).trace = ∑ j, (Sig j j
        + ((N : ℝ)⁻¹ * ∑ i, (ξh i j - μ j) * (ξh i j - μ j) - Sig j j)
        - ((sampleMean ξh - μ) j) ^ 2) := by
      unfold Matrix.trace
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Matrix.diag_apply]
      have := hent j j; rw [sq]; linarith
    have hWs : ∑ j, ((N : ℝ)⁻¹ * ∑ i, (ξh i j - μ j) * (ξh i j - μ j) - Sig j j)
        ≤ m * (κ * ε) := by
      calc _ ≤ ∑ _j : Fin m, κ * ε := Finset.sum_le_sum (fun j _ => (abs_le.mp (hW j j)).2)
        _ = m * (κ * ε) := by simp
    have htr : Sig.trace = ∑ j, Sig j j := rfl
    rw [htrSh, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hT
    have hε1 : 1 ≤ ε := by linarith
    have hfin : ε + 2 * Sig.trace ≤ ε ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hbig hε.le, mul_nonneg htrS (sub_nonneg.mpr hε1)]
    have hκmε : m * (κ * ε) ≤ ε := by nlinarith
    linarith
  · push_neg at hbig
    have hκε : κ * ε ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hbig.le hκ.le]
    have hκε0 : 0 ≤ κ * ε := by positivity
    have habs : ∀ j k, |sampleCov ξh j k - Sig j k| ≤ 2 * (κ * ε) := by
      intro j k
      rw [hent j k]
      have h2 : |(sampleMean ξh - μ) j * (sampleMean ξh - μ) k| ≤ κ * ε := by
        rw [abs_mul]
        calc |(sampleMean ξh - μ) j| * |(sampleMean ξh - μ) k| ≤ (κ * ε) * (κ * ε) :=
              mul_le_mul (hdb j) (hdb k) (abs_nonneg _) hκε0
          _ ≤ κ * ε := by nlinarith
      have a1 := abs_le.mp (hW j k)
      have a2 := abs_le.mp h2
      rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    have hfro : ((sampleCov ξh - Sig)ᵀ * (sampleCov ξh - Sig)).trace
        ≤ m ^ 2 * (2 * (κ * ε)) ^ 2 := by
      have e : ((sampleCov ξh - Sig)ᵀ * (sampleCov ξh - Sig)).trace
          = ∑ j, ∑ k, (sampleCov ξh - Sig) k j ^ 2 := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
      rw [e]
      calc _ ≤ ∑ _j : Fin m, ∑ _k : Fin m, (2 * (κ * ε)) ^ 2 := by
            refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_))
            rw [Matrix.sub_apply, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (habs k j) 2
        _ = m ^ 2 * (2 * (κ * ε)) ^ 2 := by simp; ring
    have hker' : ∀ x, Sig *ᵥ x = 0 → sampleCov ξh *ᵥ x = 0 := by
      intro x hx
      have hY : ∀ i, (fun k => ξh i k - μ k) ⬝ᵥ x = 0 := fun i =>
        ker_orth Sig hS x _ hx (fun j hj => hker i j hj)
      have hD : ∑ k, (sampleMean ξh - μ) k * x k = 0 := by
        simp only [mean_coord hN]
        have : ∑ k, ((N : ℝ)⁻¹ * ∑ i, (ξh i k - μ k)) * x k
            = (N : ℝ)⁻¹ * ∑ i, (fun k => ξh i k - μ k) ⬝ᵥ x := by
          simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))
        rw [this]; simp [hY]
      have hv : ∀ i, ∑ k, (ξh i - sampleMean ξh) k * x k = 0 := by
        intro i
        have h1 := hY i
        simp only [dotProduct] at h1
        have e : ∀ k, (ξh i - sampleMean ξh) k * x k
            = (ξh i k - μ k) * x k - (sampleMean ξh - μ) k * x k := by
          intro k; rw [PiLp.sub_apply, PiLp.sub_apply]; ring
        rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_sub_distrib, h1, hD, sub_zero]
      funext j
      simp only [Matrix.mulVec, dotProduct, sampleCov, Matrix.of_apply, Pi.zero_apply,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      calc ∑ k, (N : ℝ)⁻¹ * ((ξh i - sampleMean ξh) j * (ξh i - sampleMean ξh) k) * x k
          = (N : ℝ)⁻¹ * (ξh i - sampleMean ξh) j * ∑ k, (ξh i - sampleMean ξh) k * x k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by ring)
        _ = 0 := by rw [hv i, mul_zero]
    have hT1 := bures_le_sqrt_dist (sampleCov ξh) Sig hSh hS
    have hT2 := sqrt_dist_le (sampleCov ξh) Sig hSh hS lam hlam hker' hgap
    have hT3 : ((CFC.sqrt (sampleCov ξh) - CFC.sqrt Sig) *
        (CFC.sqrt (sampleCov ξh) - CFC.sqrt Sig)).trace ≤ m ^ 2 * (2 * (κ * ε)) ^ 2 / lam := by
      rw [le_div_iff₀ hlam]; linarith
    have hfin : m * (κ * ε) ^ 2 + m ^ 2 * (2 * (κ * ε)) ^ 2 / lam ≤ ε ^ 2 := by
      have e2 : (m : ℝ) * (κ * ε) ^ 2 + m ^ 2 * (2 * (κ * ε)) ^ 2 / lam
          = κ ^ 2 * (m + 4 * m ^ 2 / lam) * ε ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [e2]
      nlinarith [mul_le_mul_of_nonneg_right hκ2 (sq_nonneg ε)]
    linarith

lemma int_of_bound {E : Type*} [MeasurableSpace E] (P : Measure E) (f : E → ℝ)
    (hfm : Measurable f) (u : E → ℝ) (τ : ℝ) (hτ : 1 ≤ τ) (hb : ∀ x, |f x| ≤ u x)
    (hint : Integrable (fun x => Real.exp (τ * u x)) P) :
    Integrable f P ∧ Integrable (fun x => Real.exp (τ * |f x|)) P ∧
      ∫ x, Real.exp (τ * |f x|) ∂P ≤ ∫ x, Real.exp (τ * u x) ∂P := by
  have h1 : ∀ x, Real.exp (τ * |f x|) ≤ Real.exp (τ * u x) := fun x =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb x) (by linarith))
  have hi2 : Integrable (fun x => Real.exp (τ * |f x|)) P := by
    refine hint.mono' (Measurable.exp ((continuous_abs.measurable.comp hfm).const_mul τ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact h1 x
  refine ⟨?_, hi2, integral_mono hi2 hint h1⟩
  refine hi2.mono' hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have h2 := Real.add_one_le_exp (τ * |f x|)
  have h3 : |f x| ≤ τ * |f x| := le_mul_of_one_le_left (abs_nonneg _) hτ
  linarith

open WassersteinDRO.GelbrichFiniteSample in
lemma cov_facts {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) (hmc : HasMeanCov P μ Sig)
    (hY : ∀ j, Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => ξ j - μ j) P) :
    (∀ j k, ∫ ξ, (ξ j - μ j) * (ξ k - μ k) ∂P = Sig j k) ∧
    (∀ j, ∫ ξ, (ξ j - μ j) ∂P = 0) := by
  obtain ⟨hL, hmean, hcov⟩ := hmc
  have hi : Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => ξ) P := hL.integrable one_le_two
  refine ⟨fun j k => ?_, fun j => ?_⟩
  · have := congrFun (congrFun hcov j) k
    simp only [covMat, Matrix.of_apply, hmean, PiLp.sub_apply] at this
    exact this
  · have hj : Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => ξ j) P := by
      exact ((hY j).add (integrable_const (μ j))).congr
        (Filter.Eventually.of_forall fun ξ => by simp)
    rw [integral_sub hj (integrable_const _), ← coord_integral P hi j,
      show (∫ ξ, ξ ∂P) = μ from hmean]
    simp

lemma quad_integral {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m)))
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (hYY : ∀ j k, Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => (ξ j - μ j) * (ξ k - μ k)) P)
    (hcov : ∀ j k, ∫ ξ, (ξ j - μ j) * (ξ k - μ k) ∂P = Sig j k) (v : Fin m → ℝ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => (v ⬝ᵥ fun k => ξ k - μ k) ^ 2) P ∧
    ∫ ξ, (v ⬝ᵥ fun k => ξ k - μ k) ^ 2 ∂P = v ⬝ᵥ (Sig *ᵥ v) := by
  have e : ∀ ξ : EuclideanSpace ℝ (Fin m), (v ⬝ᵥ fun k => ξ k - μ k) ^ 2
      = ∑ j, ∑ k, (v j * v k) * ((ξ j - μ j) * (ξ k - μ k)) := by
    intro ξ
    simp only [dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
  have hint : ∀ j k, Integrable
      (fun ξ : EuclideanSpace ℝ (Fin m) => (v j * v k) * ((ξ j - μ j) * (ξ k - μ k))) P :=
    fun j k => (hYY j k).const_mul _
  simp_rw [e]
  refine ⟨integrable_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hint j k)), ?_⟩
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hint j k))]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finset_sum _ (fun k _ => hint j k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_const_mul, hcov]; ring

lemma ae_orth {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m)))
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (hYY : ∀ j k, Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => (ξ j - μ j) * (ξ k - μ k)) P)
    (hcov : ∀ j k, ∫ ξ, (ξ j - μ j) * (ξ k - μ k) ∂P = Sig j k) (v : Fin m → ℝ)
    (hv : v ⬝ᵥ (Sig *ᵥ v) = 0) :
    ∀ᵐ ξ ∂P, (v ⬝ᵥ fun k => ξ k - μ k) = 0 := by
  obtain ⟨hi, he⟩ := quad_integral P μ Sig hYY hcov v
  rw [hv] at he
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ξ => sq_nonneg _) hi).mp he
  filter_upwards [h0] with ξ hξ
  simpa using hξ

lemma sig_psd {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m)))
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (hYY : ∀ j k, Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => (ξ j - μ j) * (ξ k - μ k)) P)
    (hcov : ∀ j k, ∫ ξ, (ξ j - μ j) * (ξ k - μ k) ∂P = Sig j k) : Sig.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext (fun j k => ?_), fun x => ?_⟩
  · rw [star_trivial, ← hcov, ← hcov]
    congr 1; funext ξ; ring
  · rw [star_trivial, ← (quad_integral P μ Sig hYY hcov x).2]
    exact integral_nonneg (fun ξ => sq_nonneg _)

lemma coord_le {m : ℕ} (ξ : EuclideanSpace ℝ (Fin m)) (j : Fin m) : |ξ j| ≤ ‖ξ‖ := by
  have h1 : ξ j ^ 2 ≤ ∑ i, ξ i ^ 2 :=
    Finset.single_le_sum (f := fun i => ξ i ^ 2) (fun i _ => sq_nonneg (ξ i)) (Finset.mem_univ j)
  rw [← EuclideanSpace.real_norm_sq_eq] at h1
  have := sq_le_sq.mp h1
  rwa [abs_norm] at this

lemma boundY {m : ℕ} (μ ξ : EuclideanSpace ℝ (Fin m)) (j : Fin m) (C : ℝ) (hC : 1 + ‖μ‖ ≤ C) :
    |ξ j - μ j| ≤ C * (1 + ‖ξ‖ ^ 2) := by
  have h1 : |ξ j - μ j| ≤ ‖ξ - μ‖ := by rw [← PiLp.sub_apply]; exact coord_le _ j
  have h2 := norm_sub_le ξ μ
  have h3 : ‖ξ‖ ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg (‖ξ‖ - 1)]
  have h4 : 0 ≤ ‖μ‖ * ‖ξ‖ ^ 2 := by positivity
  have h5 : (1 + ‖μ‖) * (1 + ‖ξ‖ ^ 2) ≤ C * (1 + ‖ξ‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  nlinarith

lemma boundYY {m : ℕ} (μ ξ : EuclideanSpace ℝ (Fin m)) (j k : Fin m) (σ s C : ℝ)
    (hσ : |σ| ≤ s) (hC : 2 + 2 * ‖μ‖ ^ 2 + s ≤ C) :
    |(ξ j - μ j) * (ξ k - μ k) - σ| ≤ C * (1 + ‖ξ‖ ^ 2) := by
  have hj : |ξ j - μ j| ≤ ‖ξ‖ + ‖μ‖ := by
    rw [← PiLp.sub_apply]; exact (coord_le _ j).trans (norm_sub_le ξ μ)
  have hk : |ξ k - μ k| ≤ ‖ξ‖ + ‖μ‖ := by
    rw [← PiLp.sub_apply]; exact (coord_le _ k).trans (norm_sub_le ξ μ)
  have hp : |(ξ j - μ j) * (ξ k - μ k)| ≤ 2 * ‖ξ‖ ^ 2 + 2 * ‖μ‖ ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul hj hk (abs_nonneg _) (by positivity)
    nlinarith [sq_nonneg (‖ξ‖ - ‖μ‖)]
  have hs : 0 ≤ s := (abs_nonneg σ).trans hσ
  have a1 := abs_le.mp hp
  have a2 := abs_le.mp hσ
  have hfin : 2 * ‖ξ‖ ^ 2 + 2 * ‖μ‖ ^ 2 + s ≤ C * (1 + ‖ξ‖ ^ 2) := by
    have h5 : (2 + 2 * ‖μ‖ ^ 2 + s) * (1 + ‖ξ‖ ^ 2) ≤ C * (1 + ‖ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    nlinarith [sq_nonneg ‖ξ‖, sq_nonneg ‖μ‖, mul_nonneg hs (sq_nonneg ‖ξ‖),
      mul_nonneg (sq_nonneg ‖μ‖) (sq_nonneg ‖ξ‖)]
  rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

lemma meas_coord {m : ℕ} (j : Fin m) :
    Measurable (fun ξ : EuclideanSpace ℝ (Fin m) => ξ j) := by
  exact (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin m => ℝ) j).continuous.measurable

lemma fam_bound {m : ℕ} (μ ξ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) (C : ℝ)
    (hC : (1 + ‖μ‖) + (2 + 2 * ‖μ‖ ^ 2) + ∑ j, ∑ k, |Sig j k| ≤ C) (j k : Fin m) :
    |ξ j - μ j| ≤ C * (1 + ‖ξ‖ ^ 2) ∧
    |(ξ j - μ j) * (ξ k - μ k) - Sig j k| ≤ C * (1 + ‖ξ‖ ^ 2) ∧
    |(ξ j - μ j) * (ξ k - μ k)| ≤ C * (1 + ‖ξ‖ ^ 2) := by
  have hs0 : 0 ≤ ∑ j, ∑ k, |Sig j k| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs : |Sig j k| ≤ ∑ j, ∑ k, |Sig j k| :=
    (Finset.single_le_sum (f := fun k' => |Sig j k'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans
    (Finset.single_le_sum (f := fun j' => ∑ k', |Sig j' k'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j))
  have hμ : 0 ≤ ‖μ‖ ^ 2 := sq_nonneg _
  have hμ1 : 0 ≤ ‖μ‖ := norm_nonneg _
  refine ⟨boundY μ ξ j C (by linarith), boundYY μ ξ j k (Sig j k) _ C hs (by linarith), ?_⟩
  have := boundYY μ ξ j k 0 (∑ j, ∑ k, |Sig j k|) C (by rw [abs_zero]; exact hs0) (by linarith)
  rwa [sub_zero] at this

noncomputable def fam {m : ℕ} (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (a : Bool × (Fin m ⊕ Fin m × Fin m)) (ξ : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (if a.1 then 1 else -1) * Sum.elim (fun j => ξ j - μ j)
    (fun p : Fin m × Fin m => (ξ p.1 - μ p.1) * (ξ p.2 - μ p.2) - Sig p.1 p.2) a.2

lemma fam_meas {m : ℕ} (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (a : Bool × (Fin m ⊕ Fin m × Fin m)) : Measurable (fam μ Sig a) := by
  rcases a with ⟨b, j | ⟨j, k⟩⟩
  · exact ((meas_coord j).sub_const (μ j)).const_mul _
  · exact ((((meas_coord j).sub_const (μ j)).mul ((meas_coord k).sub_const (μ k))).sub_const _).const_mul _

lemma fam_abs {m : ℕ} (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) (C : ℝ)
    (hC : (1 + ‖μ‖) + (2 + 2 * ‖μ‖ ^ 2) + ∑ j, ∑ k, |Sig j k| ≤ C)
    (a : Bool × (Fin m ⊕ Fin m × Fin m)) (ξ : EuclideanSpace ℝ (Fin m)) :
    |fam μ Sig a ξ| ≤ C * (1 + ‖ξ‖ ^ 2) := by
  have h1 : ∀ b : Bool, |(if b = true then (1:ℝ) else -1)| = 1 := by
    intro b; cases b <;> simp
  rcases a with ⟨b, j | ⟨j, k⟩⟩
  · show |(if b = true then (1:ℝ) else -1) * (ξ j - μ j)| ≤ _
    rw [abs_mul, h1, one_mul]; exact (fam_bound μ ξ Sig C hC j j).1
  · show |(if b = true then (1:ℝ) else -1) * ((ξ j - μ j) * (ξ k - μ k) - Sig j k)| ≤ _
    rw [abs_mul, h1, one_mul]; exact (fam_bound μ ξ Sig C hC j k).2.1

lemma fam_int0 {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P]
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (hYY : ∀ j k, Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => (ξ j - μ j) * (ξ k - μ k)) P)
    (hcov : ∀ j k, ∫ ξ, (ξ j - μ j) * (ξ k - μ k) ∂P = Sig j k)
    (hmean : ∀ j, ∫ ξ, (ξ j - μ j) ∂P = 0) (a : Bool × (Fin m ⊕ Fin m × Fin m)) :
    ∫ ξ, fam μ Sig a ξ ∂P = 0 := by
  rcases a with ⟨b, j | ⟨j, k⟩⟩
  · show ∫ ξ, (if b = true then (1:ℝ) else -1) * (ξ j - μ j) ∂P = 0
    rw [integral_const_mul, hmean j, mul_zero]
  · show ∫ ξ, (if b = true then (1:ℝ) else -1) * ((ξ j - μ j) * (ξ k - μ k) - Sig j k) ∂P = 0
    rw [integral_const_mul, integral_sub (hYY j k) (integrable_const _), hcov j k]
    simp

lemma integ_all {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m)))
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) (C τ : ℝ)
    (hC : (1 + ‖μ‖) + (2 + 2 * ‖μ‖ ^ 2) + ∑ j, ∑ k, |Sig j k| ≤ C) (hτ : 1 ≤ τ)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => Real.exp (τ * (C * (1 + ‖ξ‖ ^ 2)))) P) :
    (∀ j, Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => ξ j - μ j) P) ∧
    (∀ j k, Integrable (fun ξ : EuclideanSpace ℝ (Fin m) => (ξ j - μ j) * (ξ k - μ k)) P) ∧
    (∀ a, Integrable (fun ξ => Real.exp (τ * |fam μ Sig a ξ|)) P ∧
      ∫ ξ, Real.exp (τ * |fam μ Sig a ξ|) ∂P ≤
        ∫ ξ, Real.exp (τ * (C * (1 + ‖ξ‖ ^ 2))) ∂P) :=
  ⟨fun j => (int_of_bound P _ ((meas_coord j).sub_const _) (fun ξ => C * (1 + ‖ξ‖ ^ 2)) τ hτ
      (fun ξ => (fam_bound μ ξ Sig C hC j j).1) hint).1,
   fun j k => (int_of_bound P _ (((meas_coord j).sub_const _).mul ((meas_coord k).sub_const _))
      (fun ξ => C * (1 + ‖ξ‖ ^ 2)) τ hτ (fun ξ => (fam_bound μ ξ Sig C hC j k).2.2) hint).1,
   fun a => (int_of_bound P _ (fam_meas μ Sig a) (fun ξ => C * (1 + ‖ξ‖ ^ 2)) τ hτ
      (fun ξ => fam_abs μ Sig C hC a ξ) hint).2⟩

lemma union_chernoff {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (hfm : ∀ a, Measurable (f a)) (κ : ℝ) (hκ : 0 < κ)
    (K : ℝ) (hint : ∀ a, Integrable (fun x => Real.exp ((1 + κ⁻¹) * |f a x|)) P)
    (hK : ∀ a, ∫ x, Real.exp ((1 + κ⁻¹) * |f a x|) ∂P ≤ K) (h0 : ∀ a, ∫ x, f a x ∂P = 0)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) :
    Measure.pi (fun _ : Fin N => P) {x | ∃ a, κ * ε * N ≤ ∑ i, f a (x i)}
      ≤ (Fintype.card ι : ENNReal) *
          ENNReal.ofReal (Real.exp (2 * K / κ ^ 2 - ε * Real.sqrt N)) := by
  rw [Set.setOf_exists]
  calc _ ≤ ∑ a, Measure.pi (fun _ : Fin N => P) {x | κ * ε * N ≤ ∑ i, f a (x i)} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _a : ι, ENNReal.ofReal (Real.exp (2 * K / κ ^ 2 - ε * Real.sqrt N)) :=
        Finset.sum_le_sum fun a _ =>
          chernoff_pi P (f a) (hfm a) κ hκ K (hint a) (hK a) (h0 a) N hN ε
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma prob_of_compl {X : Type*} [MeasurableSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    (S : Set X) (hS : MeasurableSet S) (η : ℝ) (hη : 0 ≤ η)
    (h : Q Sᶜ ≤ ENNReal.ofReal η) : ENNReal.ofReal (1 - η) ≤ Q S := by
  have e := prob_compl_eq_one_sub (μ := Q) hS.compl
  rw [compl_compl] at e
  rw [e, ENNReal.ofReal_sub _ hη, ENNReal.ofReal_one]
  exact tsub_le_tsub_left h 1

lemma eps_facts (M a η ε : ℝ) (N : ℕ) (hM : 0 ≤ M) (hN : 0 < N) (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : Real.log ((2 + M * Real.exp a) / η) / Real.sqrt N ≤ ε) :
    0 < ε ∧ M * Real.exp (a - ε * Real.sqrt N) ≤ η := by
  have hMa : 0 ≤ M * Real.exp a := mul_nonneg hM (Real.exp_pos a).le
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (Nat.cast_pos.2 hN)
  have hcη : 1 < (2 + M * Real.exp a) / η := by rw [lt_div_iff₀ hη]; linarith
  have hlog : 0 < Real.log ((2 + M * Real.exp a) / η) := Real.log_pos hcη
  have h1 : Real.log ((2 + M * Real.exp a) / η) ≤ ε * Real.sqrt N := (div_le_iff₀ hsN).1 hε
  refine ⟨?_, ?_⟩
  · by_contra hneg
    push_neg at hneg
    nlinarith
  · have h2 : (2 + M * Real.exp a) / η ≤ Real.exp (ε * Real.sqrt N) := by
      calc (2 + M * Real.exp a) / η = Real.exp (Real.log ((2 + M * Real.exp a) / η)) :=
            (Real.exp_log (by linarith)).symm
        _ ≤ _ := Real.exp_le_exp.2 h1
    have h3 := (div_le_iff₀ hη).1 h2
    rw [Real.exp_sub, ← mul_div_assoc, div_le_iff₀ (Real.exp_pos _)]
    nlinarith

lemma kappa_facts (E0 a b : ℝ) (h0 : 1 ≤ E0) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ κ : ℝ, 0 < κ ∧ κ * E0 ≤ 1 ∧ κ * a ≤ 1 ∧ κ ^ 2 * (a + b) ≤ 1 := by
  have hT : 0 < E0 + a + 1 + b := by linarith
  refine ⟨1 / (E0 + a + 1 + b), by positivity, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, one_mul, div_le_one hT]; linarith
  · rw [div_mul_eq_mul_div, one_mul, div_le_one hT]; linarith
  · rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith [mul_nonneg hT.le (by linarith : (0:ℝ) ≤ E0 + a + 1 + b - 1)]

lemma gap_exists {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (hS : Sig.PosSemidef) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ j, hS.1.eigenvalues j = 0 ∨ lam ≤ hS.1.eigenvalues j := by
  have hnn : ∀ j, 0 ≤ (if hS.1.eigenvalues j = 0 then (0:ℝ) else (hS.1.eigenvalues j)⁻¹) := by
    intro j; split_ifs
    · exact le_rfl
    · exact inv_nonneg.2 (hS.eigenvalues_nonneg j)
  have hsum : 0 ≤ ∑ j, (if hS.1.eigenvalues j = 0 then (0:ℝ) else (hS.1.eigenvalues j)⁻¹) :=
    Finset.sum_nonneg fun j _ => hnn j
  refine ⟨1 / (1 + ∑ j, (if hS.1.eigenvalues j = 0 then (0:ℝ) else (hS.1.eigenvalues j)⁻¹)),
    by positivity, fun j => ?_⟩
  by_cases h : hS.1.eigenvalues j = 0
  · exact Or.inl h
  · right
    have hpos : 0 < hS.1.eigenvalues j := lt_of_le_of_ne (hS.eigenvalues_nonneg j) (Ne.symm h)
    have hle : (hS.1.eigenvalues j)⁻¹ ≤
        ∑ j, (if hS.1.eigenvalues j = 0 then (0:ℝ) else (hS.1.eigenvalues j)⁻¹) := by
      have := Finset.single_le_sum
        (f := fun j => if hS.1.eigenvalues j = 0 then (0:ℝ) else (hS.1.eigenvalues j)⁻¹)
        (fun j _ => hnn j) (Finset.mem_univ j)
      simpa only [if_neg h] using this
    rw [div_le_iff₀ (by linarith), mul_add, mul_one]
    have e : hS.1.eigenvalues j * (hS.1.eigenvalues j)⁻¹ = 1 := mul_inv_cancel₀ h
    have := mul_le_mul_of_nonneg_left hle hpos.le
    linarith

lemma avg_abs_le (N : ℕ) (hN : 0 < N) (s t : ℝ) (h1 : s < t * N) (h2 : -s < t * N) :
    |(N : ℝ)⁻¹ * s| ≤ t := by
  have hNp : (0:ℝ) < N := Nat.cast_pos.2 hN
  rw [inv_mul_eq_div, abs_div, abs_of_pos hNp, div_le_iff₀ hNp, abs_le]
  constructor <;> linarith

lemma avg_sub_YY {m N : ℕ} (hN : 0 < N) (x : Fin N → EuclideanSpace ℝ (Fin m))
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) (j k : Fin m) :
    (N : ℝ)⁻¹ * ∑ i, (x i j - μ j) * (x i k - μ k) - Sig j k
      = (N : ℝ)⁻¹ * ∑ i, ((x i j - μ j) * (x i k - μ k) - Sig j k) := by
  have hN' : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 hN).ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_sub, ← mul_assoc, inv_mul_cancel₀ hN', one_mul]

lemma fam_inl {m N : ℕ} (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin N → EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    ∑ i, fam μ Sig (true, Sum.inl j) (x i) = ∑ i, (x i j - μ j) ∧
    ∑ i, fam μ Sig (false, Sum.inl j) (x i) = -∑ i, (x i j - μ j) := by
  constructor
  · exact Finset.sum_congr rfl fun i _ => by simp [fam]
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [fam]

lemma fam_inr {m N : ℕ} (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin N → EuclideanSpace ℝ (Fin m)) (j k : Fin m) :
    ∑ i, fam μ Sig (true, Sum.inr (j, k)) (x i)
      = ∑ i, ((x i j - μ j) * (x i k - μ k) - Sig j k) ∧
    ∑ i, fam μ Sig (false, Sum.inr (j, k)) (x i)
      = -∑ i, ((x i j - μ j) * (x i k - μ k) - Sig j k) := by
  constructor
  · exact Finset.sum_congr rfl fun i _ => by simp [fam]
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [fam]

end G21Aux

set_option maxHeartbeats 1000000 in
open MeasureTheory WassersteinDRO.GelbrichFiniteSample in
theorem solution (m : ℕ) (α A : ℝ) (hα : 2 < α) (hA : 0 < A)
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) :
    ∃ c : ℝ, 1 < c ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P],
        HasMeanCov P μ Sig →
        ∫⁻ ξ, ENNReal.ofReal (Real.exp (‖ξ‖ ^ α)) ∂P ≤ ENNReal.ofReal A →
        ∀ (N : ℕ), 0 < N → ∀ (η : ℝ), 0 < η → η ≤ 1 →
        ∀ (ε : ℝ), Real.log (c / η) / Real.sqrt N ≤ ε →
        ∃ S : Set (Fin N → EuclideanSpace ℝ (Fin m)), MeasurableSet S ∧
          S ⊆ {ξh | (μ, Sig) ∈ uncertaintySet ε (sampleMean ξh) (sampleCov ξh)} ∧
          ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P) S := by
  have hC0 : 0 ≤ (1 + ‖μ‖) + (2 + 2 * ‖μ‖ ^ 2) + ∑ j, ∑ k, |Sig j k| := by positivity
  set C : ℝ := (1 + ‖μ‖) + (2 + 2 * ‖μ‖ ^ 2) + ∑ j, ∑ k, |Sig j k| with hCdef
  by_cases hS : Sig.PosSemidef
  swap
  · obtain ⟨K0, hK0⟩ := G21Aux.moment_bound (m := m) α A C hα hA.le hC0
    refine ⟨2, by norm_num, ?_⟩
    intro P hP hmc hmom
    exfalso
    obtain ⟨hY, hYY, -⟩ := G21Aux.integ_all P μ Sig C 1 hCdef.symm.le le_rfl
      (by simpa only [one_mul] using (hK0 P hmom).1)
    exact hS (G21Aux.sig_psd P μ Sig hYY (G21Aux.cov_facts P μ Sig hmc hY).1)
  obtain ⟨lam, hlam, hgap⟩ := G21Aux.gap_exists Sig hS
  have hE0 : 1 ≤ 1 + 2 * Sig.trace := by linarith [hS.trace_nonneg]
  obtain ⟨κ, hκ, hκ1, hκm, hκ2⟩ := G21Aux.kappa_facts (1 + 2 * Sig.trace) (m : ℝ)
    (4 * (m : ℝ) ^ 2 / lam) hE0 (Nat.cast_nonneg _) (by positivity)
  have hτ : 1 ≤ 1 + κ⁻¹ := by linarith [inv_pos.2 hκ]
  obtain ⟨K, hK⟩ := G21Aux.moment_bound (m := m) α A ((1 + κ⁻¹) * C) hα hA.le
    (mul_nonneg (by linarith) hC0)
  have hM : (0 : ℝ) ≤ ((Fintype.card (Bool × (Fin m ⊕ Fin m × Fin m)) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  refine ⟨2 + ((Fintype.card (Bool × (Fin m ⊕ Fin m × Fin m)) : ℕ) : ℝ) *
      Real.exp (2 * K / κ ^ 2),
    by linarith [mul_nonneg hM (Real.exp_pos (2 * K / κ ^ 2)).le], ?_⟩
  intro P hP hmc hmom N hN η hη hη1 ε hε
  obtain ⟨hε0, harith⟩ := G21Aux.eps_facts _ (2 * K / κ ^ 2) η ε N hM hN hη hη1 hε
  obtain ⟨hDi, hDK⟩ := hK P hmom
  have hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin m) =>
      Real.exp ((1 + κ⁻¹) * (C * (1 + ‖ξ‖ ^ 2)))) P := by
    simpa only [mul_assoc] using hDi
  have hKle : ∫ ξ, Real.exp ((1 + κ⁻¹) * (C * (1 + ‖ξ‖ ^ 2))) ∂P ≤ K := by
    simpa only [mul_assoc] using hDK
  obtain ⟨hY, hYY, hfam⟩ := G21Aux.integ_all P μ Sig C (1 + κ⁻¹) hCdef.symm.le hτ hint
  obtain ⟨hcov, hmean⟩ := G21Aux.cov_facts P μ Sig hmc hY
  have hU := G21Aux.union_chernoff P (G21Aux.fam μ Sig) (G21Aux.fam_meas μ Sig) κ hκ K
    (fun a => (hfam a).1) (fun a => (hfam a).2.trans hKle)
    (fun a => G21Aux.fam_int0 P μ Sig hYY hcov hmean a) N hN ε
  obtain ⟨w, hw⟩ : ∃ w : Fin m → Fin m → ℝ, ∀ j, w j =
      if hS.1.eigenvalues j = 0 then ⇑(hS.1.eigenvectorBasis j) else 0 := ⟨_, fun j => rfl⟩
  have hwS : ∀ j, w j ⬝ᵥ (Sig *ᵥ w j) = 0 := by
    intro j
    by_cases h : hS.1.eigenvalues j = 0
    · rw [hw j, if_pos h, hS.1.mulVec_eigenvectorBasis, h, zero_smul, dotProduct_zero]
    · rw [hw j, if_neg h, zero_dotProduct]
  have hae : ∀ j, ∀ᵐ ξ ∂P, (w j ⬝ᵥ fun k => ξ k - μ k) = 0 :=
    fun j => G21Aux.ae_orth P μ Sig hYY hcov (w j) (hwS j)
  have hgm : ∀ j, Measurable (fun ξ : EuclideanSpace ℝ (Fin m) => w j ⬝ᵥ fun k => ξ k - μ k) := by
    intro j
    simp only [dotProduct]
    exact Finset.measurable_sum _ (fun k _ => ((G21Aux.meas_coord k).sub_const _).const_mul _)
  have hfm2 : ∀ a, Measurable (fun x : Fin N → EuclideanSpace ℝ (Fin m) =>
      ∑ i, G21Aux.fam μ Sig a (x i)) := fun a =>
    Finset.measurable_sum _ (fun i _ => (G21Aux.fam_meas μ Sig a).comp (measurable_pi_apply i))
  obtain ⟨Z1, hZ1⟩ : ∃ Z : Set (Fin N → EuclideanSpace ℝ (Fin m)),
      Z = {x | ∀ i j, (w j ⬝ᵥ fun k => x i k - μ k) = 0} := ⟨_, rfl⟩
  obtain ⟨Z2, hZ2⟩ : ∃ Z : Set (Fin N → EuclideanSpace ℝ (Fin m)),
      Z = {x | ∀ a, ∑ i, G21Aux.fam μ Sig a (x i) < κ * ε * N} := ⟨_, rfl⟩
  have hZ1m : MeasurableSet Z1 := by
    rw [hZ1]; simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun ((hgm j).comp (measurable_pi_apply i)) measurable_const
  have hZ2m : MeasurableSet Z2 := by
    rw [hZ2]; simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun a => measurableSet_lt (hfm2 a) measurable_const
  refine ⟨Z1 ∩ Z2, hZ1m.inter hZ2m, ?_, ?_⟩
  · rintro x ⟨hz, hb⟩
    rw [hZ1] at hz
    rw [hZ2] at hb
    have hz' : ∀ i j, (w j ⬝ᵥ fun k => x i k - μ k) = 0 := hz
    have hb' : ∀ a, ∑ i, G21Aux.fam μ Sig a (x i) < κ * ε * N := hb
    show (μ, Sig) ∈ uncertaintySet ε (sampleMean x) (sampleCov x)
    refine G21Aux.det_bound hN x μ Sig hS lam hlam hgap κ ε hκ hε0 hκ1 hκm hκ2 ?_ ?_ ?_
    · intro j
      exact G21Aux.avg_abs_le N hN _ (κ * ε)
        (lt_of_eq_of_lt (G21Aux.fam_inl μ Sig x j).1.symm (hb' (true, Sum.inl j)))
        (lt_of_eq_of_lt (G21Aux.fam_inl μ Sig x j).2.symm (hb' (false, Sum.inl j)))
    · intro j k
      rw [G21Aux.avg_sub_YY hN x μ Sig j k]
      exact G21Aux.avg_abs_le N hN _ (κ * ε)
        (lt_of_eq_of_lt (G21Aux.fam_inr μ Sig x j k).1.symm (hb' (true, Sum.inr (j, k))))
        (lt_of_eq_of_lt (G21Aux.fam_inr μ Sig x j k).2.symm (hb' (false, Sum.inr (j, k))))
    · intro i j hβ
      have := hz' i j
      rwa [hw j, if_pos hβ] at this
  · refine G21Aux.prob_of_compl _ _ (hZ1m.inter hZ2m) η hη.le ?_
    rw [Set.compl_inter]
    have hn : Measure.pi (fun _ : Fin N => P) Z1ᶜ = 0 := by
      rw [hZ1]
      refine measure_mono_null ?_ (measure_iUnion_null fun i => measure_iUnion_null fun j =>
        Measure.pi_eval_preimage_null (fun _ : Fin N => P) (i := i) (ae_iff.mp (hae j)))
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨i, j, hij⟩ := hx
      simp only [Set.mem_iUnion, Set.mem_preimage, Function.eval, Set.mem_setOf_eq]
      exact ⟨i, j, hij⟩
    have hs2 : Z2ᶜ ⊆ {x | ∃ a, κ * ε * N ≤ ∑ i, G21Aux.fam μ Sig a (x i)} := by
      rw [hZ2]; intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hx
      exact hx
    calc Measure.pi (fun _ : Fin N => P) (Z1ᶜ ∪ Z2ᶜ)
        ≤ Measure.pi (fun _ : Fin N => P) Z1ᶜ + Measure.pi (fun _ : Fin N => P) Z2ᶜ :=
          measure_union_le _ _
      _ ≤ 0 + ((Fintype.card (Bool × (Fin m ⊕ Fin m × Fin m)) : ℕ) : ENNReal) *
            ENNReal.ofReal (Real.exp (2 * K / κ ^ 2 - ε * Real.sqrt N)) :=
          add_le_add (le_of_eq hn) ((measure_mono hs2).trans hU)
      _ = ENNReal.ofReal (((Fintype.card (Bool × (Fin m ⊕ Fin m × Fin m)) : ℕ) : ℝ) *
            Real.exp (2 * K / κ ^ 2 - ε * Real.sqrt N)) := by
          rw [zero_add, ENNReal.ofReal_mul hM, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal harith
