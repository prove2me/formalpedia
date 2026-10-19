-- Prove2me | solution 1 for RelSmoothFOM.DOptimal.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T03:17:37.008607+00:00
-- url     : https://prove2.me/submissions/88b918eb-d644-47cf-8739-a5408e0c5939

-- Licensed under Apache 2.0. Complete D-optimal design iteration-complexity theorem.
import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting


namespace DOptimalProof

noncomputable def moment {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  H * Matrix.diagonal x * H.transpose

noncomputable def leverage {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  H.transpose * (moment H x)⁻¹ * H

end DOptimalProof


namespace DOptimalProof
open Matrix

lemma transpose_injective {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (xstar : Fin n → ℝ) (hstar : (moment H xstar).PosDef) :
    Function.Injective H.transpose.mulVec := by
  intro u v huv
  have hz : H.transpose *ᵥ (u - v) = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  by_contra hne
  have hpos := hstar.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
  have he : moment H xstar *ᵥ (u - v) = 0 := by
    simp only [moment, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  rw [he, dotProduct_zero] at hpos
  exact (lt_irrefl 0) hpos

lemma moment_posDef {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (xstar : Fin n → ℝ) (hstar : (moment H xstar).PosDef)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) : (moment H x).PosDef := by
  have hd : (Matrix.diagonal x).PosDef := Matrix.PosDef.diagonal hx
  have hh := hd.conjTranspose_mul_mul_same (transpose_injective H xstar hstar)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
    moment] using hh

lemma leverage_posSemidef {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : (moment H x).PosDef) : (leverage H x).PosSemidef := by
  have hh := hx.inv.posSemidef.conjTranspose_mul_mul_same H
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, leverage] using hh

end DOptimalProof


namespace DOptimalProof
open Matrix
open scoped Matrix

lemma diagonal_inverse_product {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    Matrix.diagonal x * Matrix.diagonal (fun j => (x j)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_inv_cancel₀ (ne_of_gt (hx _)), Matrix.diagonal_one]

lemma leverage_complement_posSemidef {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hA : (moment H x).PosDef) :
    (Matrix.diagonal (fun j => (x j)⁻¹) - leverage H x).PosSemidef := by
  let D := Matrix.diagonal (fun j => (x j)⁻¹)
  have hDX : D * Matrix.diagonal x = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (ne_of_gt (hx _)), Matrix.diagonal_one]
  have hXD := diagonal_inverse_product x hx
  have hd : (Matrix.diagonal x).PosSemidef := Matrix.PosSemidef.diagonal (fun j => (hx j).le)
  have hb := hd.mul_mul_conjTranspose_same (Matrix.fromRows H D)
  have he : Matrix.fromRows H D * Matrix.diagonal x * (Matrix.fromRows H D)ᴴ =
      Matrix.fromBlocks (moment H x) H Hᴴ D := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    have hD : Dᴴ = D := by simp [D]
    rw [hD, hDX, Matrix.one_mul]
    have hHD : H * Matrix.diagonal x * D = H := by
      rw [Matrix.mul_assoc, hXD, Matrix.mul_one]
    rw [hHD, Matrix.one_mul]
    simp only [moment, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [he] at hb
  let := hA.isUnit.invertible
  have hh := (Matrix.PosDef.fromBlocks₁₁ H D hA).mp hb
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, leverage] using hh

lemma leverage_square_bounds {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hA : (moment H x).PosDef) :
    (leverage H x ⊙ leverage H x).PosSemidef ∧
    (Matrix.diagonal (fun j => (x j)⁻¹) ⊙ Matrix.diagonal (fun j => (x j)⁻¹) -
      leverage H x ⊙ leverage H x).PosSemidef := by
  let C := leverage H x
  let D := Matrix.diagonal (fun j => (x j)⁻¹)
  have hC := leverage_posSemidef H x hA
  have hD : D.PosSemidef := Matrix.PosSemidef.diagonal (fun j => (inv_pos.mpr (hx j)).le)
  have hDC := leverage_complement_posSemidef H x hx hA
  refine ⟨hC.hadamard hC, ?_⟩
  have hh := (hDC.hadamard hD).add (hC.hadamard hDC)
  convert hh using 1 <;> try rfl
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.hadamard_apply, D]
  ring

end DOptimalProof


namespace DOptimalProof
open Matrix
open scoped Matrix

lemma trace_diagonal_square {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsHermitian) (z : Fin n → ℝ) :
    (C * Matrix.diagonal z * C * Matrix.diagonal z).trace =
      z ⬝ᵥ ((C ⊙ C) *ᵥ z) := by
  change (∑ i, (C * Matrix.diagonal z * C * Matrix.diagonal z) i i) = _
  simp only [Matrix.mul_diagonal]
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal]
  have hs : C j i = C i j := by simpa using hC.apply i j
  rw [hs]
  ring

lemma trace_moment_square {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x z : Fin n → ℝ) (hx : (moment H x).PosDef) :
    ((moment H x)⁻¹ * moment H z * (moment H x)⁻¹ * moment H z).trace =
      z ⬝ᵥ ((leverage H x ⊙ leverage H x) *ᵥ z) := by
  have he : ((moment H x)⁻¹ * moment H z * (moment H x)⁻¹ * moment H z).trace =
      (leverage H x * Matrix.diagonal z * leverage H x * Matrix.diagonal z).trace := by
    calc
      _ = (((moment H x)⁻¹ * moment H z * (moment H x)⁻¹ * H * Matrix.diagonal z) * H.transpose).trace := by
        congr 1
        simp only [moment, Matrix.mul_assoc]
      _ = (H.transpose * ((moment H x)⁻¹ * moment H z * (moment H x)⁻¹ * H * Matrix.diagonal z)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by
        congr 1
        simp only [leverage, moment, Matrix.mul_assoc]
  rw [he]
  exact trace_diagonal_square _ (leverage_posSemidef H x hx).isHermitian z

lemma diagonal_square_form {n : ℕ} (x z : Fin n → ℝ) :
    z ⬝ᵥ ((Matrix.diagonal (fun j => (x j)⁻¹) ⊙ Matrix.diagonal (fun j => (x j)⁻¹)) *ᵥ z) =
      ∑ j, (z j / x j)^2 := by
  simp only [Matrix.diagonal_hadamard_diagonal, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply, div_eq_mul_inv]
  ring

lemma objective_curvature_bounds {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x z : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hA : (moment H x).PosDef) :
    0 ≤ ((moment H x)⁻¹ * moment H z * (moment H x)⁻¹ * moment H z).trace ∧
    ((moment H x)⁻¹ * moment H z * (moment H x)⁻¹ * moment H z).trace ≤
      ∑ j, (z j / x j)^2 := by
  rw [trace_moment_square H x z hA]
  obtain ⟨hl, hu⟩ := leverage_square_bounds H x hx hA
  have h1 := hl.dotProduct_mulVec_nonneg z
  have h2 := hu.dotProduct_mulVec_nonneg z
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at h1 h2
  rw [diagonal_square_form] at h2
  exact ⟨h1, sub_nonneg.mp h2⟩

end DOptimalProof


namespace DOptimalProof

open Matrix Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem differentiable_det_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix ι ι ℝ} (hA : ∀ i j, Differentiable ℝ (fun x => A x i j)) :
    Differentiable ℝ (fun x => (A x).det) := by
  simp only [Matrix.det_apply']
  apply Differentiable.fun_sum
  intro σ _
  apply Differentiable.const_mul
  have hp (s : Finset ι) : Differentiable ℝ (fun x => ∏ i ∈ s, A x (σ i) i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (differentiable_const (1 : ℝ))
    | @insert i s hi ih =>
        simp only [Finset.prod_insert hi]
        convert (hA (σ i) i).mul ih using 1 <;> rfl
  exact hp Finset.univ

theorem det_polynomial_eval (B : Matrix ι ι ℝ) (t : ℝ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • B.map Polynomial.C)).eval t =
      (1 + t • B).det := by
  change (Polynomial.evalRingHom t) _ = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change Polynomial.eval t ((if i = j then 1 else 0) +
      Polynomial.X * Polynomial.C (B i j)) = (if i = j then 1 else 0) + t * B i j
  by_cases hij : i = j <;> simp [hij] <;> ring

theorem det_one_add_derivative (B : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • B).det) B.trace 0 := by
  have h := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • B.map Polynomial.C)).hasDerivAt 0
  rw [Matrix.derivative_det_one_add_X_smul] at h
  simpa only [det_polynomial_eval] using h

theorem det_affine_derivative_zero (A B : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (A + t • B).det) (A.det * (A⁻¹ * B).trace) 0 := by
  have h := (det_one_add_derivative (A⁻¹ * B)).const_mul A.det
  have he (t : ℝ) : A.det * (1 + t • (A⁻¹ * B)).det = (A + t • B).det := by
    rw [← Matrix.det_mul, mul_add, mul_one, Matrix.mul_smul, ← mul_assoc,
      Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), one_mul]
  simpa only [he] using h

theorem det_affine_derivative (A B : Matrix ι ι ℝ) (t : ℝ)
    (hA : (A + t • B).det ≠ 0) :
    HasDerivAt (fun s : ℝ => (A + s • B).det)
      ((A + t • B).det * ((A + t • B)⁻¹ * B).trace) t := by
  have hd : HasDerivAt (fun s : ℝ => s - t) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const t
  have hz : HasDerivAt (fun s : ℝ => (A + t • B + s • B).det)
      ((A + t • B).det * ((A + t • B)⁻¹ * B).trace) (t - t) := by
    simpa only [sub_self] using det_affine_derivative_zero (A + t • B) B hA
  have h := HasDerivAt.comp (h := fun s : ℝ => s - t) t hz hd
  have he (s : ℝ) : A + t • B + (s - t) • B = A + s • B := by module
  simpa only [Function.comp_def, sub_self, mul_one, he] using h

theorem neg_logdet_affine_derivative (A B : Matrix ι ι ℝ) (t : ℝ)
    (hA : (A + t • B).det ≠ 0) :
    HasDerivAt (fun s : ℝ => -Real.log (A + s • B).det)
      (-((A + t • B)⁻¹ * B).trace) t := by
  have h := ((det_affine_derivative A B t hA).log hA).neg
  convert h using 1 <;> first | rfl | field_simp

end DOptimalProof


namespace DOptimalProof

open Matrix
open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_affine_derivative (A B : Matrix ι ι ℝ) (t : ℝ)
    (hA : (A + t • B).det ≠ 0) :
    HasDerivAt (fun s : ℝ => (A + s • B)⁻¹)
      (-((A + t • B)⁻¹ * B * (A + t • B)⁻¹)) t := by
  have hu : IsUnit (A + t • B) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA)
  obtain ⟨u, hu⟩ := hu
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  simp only [Matrix.coe_units_inv, hu] at hi
  have hd := hi.comp_hasDerivAt t (((hasDerivAt_id t).smul_const B).const_add A)
  simp only [Function.comp_def, id_eq] at hd
  have he : (fun s : ℝ => Ring.inverse (A + s • B)) =
      (fun s : ℝ => (A + s • B)⁻¹) := by
    funext s
    exact (Matrix.nonsing_inv_eq_ringInverse _).symm
  rw [he] at hd
  simp only [one_smul] at hd
  convert hd using 1 <;> rfl

theorem neg_trace_inverse_derivative (A B : Matrix ι ι ℝ) (t : ℝ)
    (hA : (A + t • B).det ≠ 0) :
    HasDerivAt (fun s : ℝ => -((A + s • B)⁻¹ * B).trace)
      (((A + t • B)⁻¹ * B * (A + t • B)⁻¹ * B).trace) t := by
  let tr : Matrix ι ι ℝ →L[ℝ] ℝ := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have hd := tr.hasFDerivAt.comp_hasDerivAt t
    ((inverse_affine_derivative A B t hA).mul_const B)
  have hn := hd.neg
  change HasDerivAt (fun s : ℝ => -((A + s • B)⁻¹ * B).trace)
    (-(-((A + t • B)⁻¹ * B * (A + t • B)⁻¹) * B).trace) t at hn
  rw [neg_mul, Matrix.trace_neg, neg_neg] at hn
  convert hn using 1

end DOptimalProof


namespace DOptimalProof

open Matrix RelSmoothFOM.DOptimal

theorem moment_entry {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (i j : Fin m) :
    moment H x i j = ∑ k, H i k * x k * H j k := by
  rw [moment, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem moment_affine {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x z : Fin n → ℝ) (t : ℝ) :
    moment H (x + t • z) = moment H x + t • moment H z := by
  ext i j
  simp only [moment_entry, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.smul_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem differentiable_moment_det {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) :
    Differentiable ℝ (fun x => (moment H x).det) := by
  apply differentiable_det_entries
  intro i j
  simp only [moment_entry]
  fun_prop

theorem differentiableAt_objective {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : (moment H x).det ≠ 0) :
    DifferentiableAt ℝ (dOptObj H) x := by
  exact ((differentiable_moment_det H x).log hx).neg

theorem objective_line_derivative {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x z : Fin n → ℝ) (t : ℝ) (hx : (moment H (x + t • z)).det ≠ 0) :
    HasDerivAt (fun s : ℝ => dOptObj H (x + s • z))
      (-((moment H (x + t • z))⁻¹ * moment H z).trace) t := by
  have ht : (moment H x + t • moment H z).det ≠ 0 := by
    simpa only [moment_affine] using hx
  change HasDerivAt (fun s : ℝ => -Real.log (moment H (x + s • z)).det)
    (-((moment H (x + t • z))⁻¹ * moment H z).trace) t
  simpa only [moment_affine] using
    neg_logdet_affine_derivative (moment H x) (moment H z) t ht

theorem objective_fderiv {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (x z : Fin n → ℝ) (hx : (moment H x).det ≠ 0) :
    fderiv ℝ (dOptObj H) x z = -((moment H x)⁻¹ * moment H z).trace := by
  have hd := (differentiableAt_objective H x hx).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x) (by simp)
  have h0 : HasDerivAt (fun s : ℝ => dOptObj H (x + s • z))
      (fderiv ℝ (dOptObj H) x z) 0 := by
    simpa only [Function.comp_def, id_eq, zero_smul, add_zero, one_smul] using hd
  have h1 := objective_line_derivative H x z 0 (by simpa only [zero_smul, add_zero] using hx)
  simpa only [zero_smul, add_zero] using h0.unique h1

theorem objective_slope_derivative {m n : ℕ}
    (H : Matrix (Fin m) (Fin n) ℝ) (x z : Fin n → ℝ) (t : ℝ)
    (hx : (moment H (x + t • z)).det ≠ 0) :
    HasDerivAt (fun s : ℝ => -((moment H (x + s • z))⁻¹ * moment H z).trace)
      (((moment H (x + t • z))⁻¹ * moment H z *
        (moment H (x + t • z))⁻¹ * moment H z).trace) t := by
  have ht : (moment H x + t • moment H z).det ≠ 0 := by
    simpa only [moment_affine] using hx
  simpa only [moment_affine] using
    neg_trace_inverse_derivative (moment H x) (moment H z) t ht

end DOptimalProof


namespace DOptimalProof

open RelSmoothFOM.DOptimal

theorem differentiableAt_barrier {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, x j ≠ 0) :
    DifferentiableAt ℝ logBarrier x := by
  apply DifferentiableAt.neg
  apply DifferentiableAt.fun_sum
  intro j _
  exact (differentiableAt_apply j x).log (hx j)

theorem coordinate_line_derivative {n : ℕ} (x z : Fin n → ℝ) (t : ℝ) (j : Fin n) :
    HasDerivAt (fun s : ℝ => x j + s * z j) (z j) t := by
  simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const (z j)).const_add (x j)

theorem barrier_line_derivative {n : ℕ} (x z : Fin n → ℝ) (t : ℝ)
    (hx : ∀ j, x j + t * z j ≠ 0) :
    HasDerivAt (fun s : ℝ => logBarrier (x + s • z))
      (-(∑ j, z j / (x j + t * z j))) t := by
  have hd := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (coordinate_line_derivative x z t j).log (hx j))).neg
  change HasDerivAt (fun s : ℝ => -(∑ j, Real.log (x j + s * z j))) _ t
  convert hd using 1 <;> rfl

theorem barrier_fderiv {n : ℕ} (x z : Fin n → ℝ) (hx : ∀ j, x j ≠ 0) :
    fderiv ℝ logBarrier x z = -(∑ j, z j / x j) := by
  have hd := (differentiableAt_barrier x hx).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x) (by simp)
  have h0 : HasDerivAt (fun s : ℝ => logBarrier (x + s • z))
      (fderiv ℝ logBarrier x z) 0 := by
    simpa only [Function.comp_def, id_eq, zero_smul, add_zero, one_smul] using hd
  have h1 := barrier_line_derivative x z 0 (by simpa only [zero_mul, add_zero] using hx)
  simpa only [zero_mul, add_zero] using h0.unique h1

theorem barrier_slope_derivative {n : ℕ} (x z : Fin n → ℝ) (t : ℝ)
    (hx : ∀ j, x j + t * z j ≠ 0) :
    HasDerivAt (fun s : ℝ => -(∑ j, z j / (x j + s * z j)))
      (∑ j, (z j / (x j + t * z j)) ^ 2) t := by
  have hd (j : Fin n) : HasDerivAt (fun s : ℝ => -(z j / (x j + s * z j)))
      ((z j / (x j + t * z j)) ^ 2) t := by
    have h := (((coordinate_line_derivative x z t j).inv (hx j)).const_mul (z j)).neg
    convert h using 1 <;> first | rfl | (field_simp [hx j])
  simpa only [Finset.sum_neg_distrib] using HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)

end DOptimalProof


namespace DOptimalProof
open RelSmoothFOM.DOptimal

lemma positive_segment {n : ℕ} {x y : Fin n → ℝ}
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ∀ j, 0 < (x + t • (y-x)) j := by
  intro j
  change 0 < x j + t * (y j - x j)
  have hp := hx j
  have hq := hy j
  have h1 := mul_nonneg (sub_nonneg.mpr ht.2) hp.le
  have h2 := mul_nonneg ht.1 hq.le
  by_cases hz : t = 0
  · simp [hz, hp]
  · have h3 := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hz)) hq
    nlinarith

lemma posSimplex_convex (n : ℕ) : Convex ℝ (posSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    change 0 < a * x j + b * y j
    have h1 := mul_nonneg ha (hx.1 j).le
    have h2 := mul_nonneg hb (hy.1 j).le
    rcases eq_or_lt_of_le ha with he | he
    · have hb1 : b = 1 := by linarith
      simp [← he, hb1, hy.1 j]
    · have h3 := mul_pos he (hx.1 j)
      linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

lemma uniform_mem {n : ℕ} (hn : 0 < n) :
    (fun _ : Fin n => 1 / (n : ℝ)) ∈ posSimplex n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro j
    exact one_div_pos.mpr hnR
  · simp [ne_of_gt hnR]

lemma mixture_mem {n : ℕ} (hn : 0 < n) {xstar : Fin n → ℝ}
    (hx : xstar ∈ stdSimplex ℝ (Fin n)) {δ : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) :
    (fun j => (1-δ)*xstar j + δ/n) ∈ posSimplex n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro j
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hd1) (hx.1 j)) (div_pos hd hnR)
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

end DOptimalProof


namespace DOptimalProof

lemma scalar_convex {f g v : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (v t) t)
    (hv : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ v t) :
    ConvexOn ℝ (Set.Icc 0 1) f := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hf t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact (hg t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact hv t (interior_subset ht)

lemma scalar_support {f g v : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (v t) t)
    (hv : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ v t) :
    f 0 + g 0 ≤ f 1 := by
  have hc := scalar_convex hf hg hv
  have hh := hc.le_slope_of_hasDerivAt (x := 0) (y := 1) (by norm_num) (by norm_num) (by norm_num)
    (hf 0 (by norm_num))
  simp only [slope_def_field, sub_zero, div_one] at hh
  linarith

end DOptimalProof


namespace DOptimalProof
open RelSmoothFOM.DOptimal RelSmoothFOM.PrimalGrad

lemma line_support_data {m n : ℕ}
    (H : Matrix (Fin m) (Fin n) ℝ) (xstar : Fin n → ℝ)
    (hstar : (moment H xstar).PosDef) (x y : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) :
    dOptObj H x + fderiv ℝ (dOptObj H) x (y-x) ≤ dOptObj H y ∧
    dOptObj H y ≤ dOptObj H x + fderiv ℝ (dOptObj H) x (y-x) + bregman logBarrier y x ∧
    0 ≤ bregman logBarrier y x := by
  let z := y-x
  let F : ℝ → ℝ := fun t => dOptObj H (x+t•z)
  let G : ℝ → ℝ := fun t => -((moment H (x+t•z))⁻¹ * moment H z).trace
  let V : ℝ → ℝ := fun t => ((moment H (x+t•z))⁻¹ * moment H z *
    (moment H (x+t•z))⁻¹ * moment H z).trace
  let B : ℝ → ℝ := fun t => logBarrier (x+t•z)
  let C : ℝ → ℝ := fun t => -(∑ j, z j / (x j+t*z j))
  let W : ℝ → ℝ := fun t => ∑ j, (z j / (x j+t*z j))^2
  have hp (t : ℝ) (ht : t ∈ Set.Icc 0 1) := positive_segment hx hy ht
  have hA (t : ℝ) (ht : t ∈ Set.Icc 0 1) := moment_posDef H xstar hstar _ (hp t ht)
  have hn (t : ℝ) (ht : t ∈ Set.Icc 0 1) : (moment H (x+t•z)).det ≠ 0 :=
    (hA t ht).det_pos.ne'
  have hc (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ∀ j, x j+t*z j ≠ 0 :=
    fun j => ne_of_gt (hp t ht j)
  have hf : ∀ t ∈ Set.Icc 0 1, HasDerivAt F (G t) t :=
    fun t ht => objective_line_derivative H x z t (hn t ht)
  have hg : ∀ t ∈ Set.Icc 0 1, HasDerivAt G (V t) t :=
    fun t ht => objective_slope_derivative H x z t (hn t ht)
  have hb : ∀ t ∈ Set.Icc 0 1, HasDerivAt B (C t) t :=
    fun t ht => barrier_line_derivative x z t (hc t ht)
  have hd : ∀ t ∈ Set.Icc 0 1, HasDerivAt C (W t) t :=
    fun t ht => barrier_slope_derivative x z t (hc t ht)
  have hv (t : ℝ) (ht : t ∈ Set.Icc 0 1) : 0 ≤ V t ∧ V t ≤ W t := by
    simpa only [V, W, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      objective_curvature_bounds H (x+t•z) z (hp t ht) (hA t ht)
  have hsF := scalar_support hf hg (fun t ht => (hv t ht).1)
  have hsB := scalar_support hb hd (fun t ht => (hv t ht).1.trans (hv t ht).2)
  have hsD := scalar_support (fun t ht => (hb t ht).sub (hf t ht))
    (fun t ht => (hd t ht).sub (hg t ht)) (fun t ht => sub_nonneg.mpr (hv t ht).2)
  have hfx := objective_fderiv H x (y-x) ((moment_posDef H xstar hstar x hx).det_pos.ne')
  have hhx := barrier_fderiv x (y-x) (fun j => (hx j).ne')
  have he : x + (y-x) = y := by abel
  simp only [F, G, B, C, z, zero_smul, add_zero, one_smul, he,
    zero_mul, Pi.sub_apply] at hsF hsB hsD
  simp only [bregman, hfx, hhx, Pi.sub_apply]
  exact ⟨hsF, by linarith, by linarith⟩

end DOptimalProof


namespace DOptimalProof
open RelSmoothFOM.DOptimal
open Filter
open scoped Topology

lemma boundary_support {m n : ℕ}
    (H : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n)
    (xstar : Fin n → ℝ) (hs : xstar ∈ stdSimplex ℝ (Fin n))
    (hstar : (moment H xstar).PosDef) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    dOptObj H a + fderiv ℝ (dOptObj H) a (xstar-a) ≤ dOptObj H xstar := by
  let r : ℕ → ℝ := fun k => 1 / ((k : ℝ)+1)
  let u : ℕ → Fin n → ℝ := fun k j => (1-r k)*xstar j + r k/n
  have hrp (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hrl (k : ℕ) : r k ≤ 1 := by
    dsimp [r]
    exact (div_le_one (by positivity)).mpr (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hu (k : ℕ) : u k ∈ posSimplex n := mixture_mem hn hs (hrp k) (hrl k)
  have hr : Tendsto r atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto u atTop (nhds xstar) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hh := ((hconst.sub hr).mul_const (xstar j)).add (hr.div_const (n : ℝ))
    simpa only [sub_zero, one_mul, zero_div, add_zero] using hh
  have hf := (differentiableAt_objective H xstar hstar.det_pos.ne').continuousAt.tendsto.comp ht
  have hl := ((fderiv ℝ (dOptObj H) a).continuous.tendsto (xstar-a)).comp (ht.sub tendsto_const_nhds)
  have hlim : Tendsto (fun k => dOptObj H (u k) -
      (dOptObj H a + fderiv ℝ (dOptObj H) a (u k-a))) atTop
      (nhds (dOptObj H xstar - (dOptObj H a + fderiv ℝ (dOptObj H) a (xstar-a)))) :=
    hf.sub (tendsto_const_nhds.add hl)
  have hz : 0 ≤ dOptObj H xstar - (dOptObj H a + fderiv ℝ (dOptObj H) a (xstar-a)) :=
    ge_of_tendsto' hlim fun k => sub_nonneg.mpr (line_support_data H xstar hstar a (u k) ha (hu k).1).1
  exact sub_nonneg.mp hz

lemma boundary_mixture_value {m n : ℕ}
    (H : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n)
    (xstar : Fin n → ℝ) (hs : xstar ∈ stdSimplex ℝ (Fin n))
    (hstar : (moment H xstar).PosDef) (δ : ℝ) (hd : 0 < δ) (hd1 : δ ≤ 1) :
    dOptObj H (fun j => (1-δ)*xstar j + δ/n) ≤
      (1-δ)*dOptObj H xstar + δ*dOptObj H (fun _ => 1/(n : ℝ)) := by
  let u : Fin n → ℝ := fun _ => 1/(n : ℝ)
  let y : Fin n → ℝ := fun j => (1-δ)*xstar j + δ/n
  have hy := mixture_mem hn hs hd hd1
  have hu := uniform_mem hn
  have h1 := boundary_support H hn xstar hs hstar y hy.1
  have h2 := (line_support_data H xstar hstar y u hy.1 hu.1).1
  have he : (1-δ) • (xstar-y) + δ • (u-y) = (0 : Fin n → ℝ) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul, u, y]
    ring
  have hm := congrArg (fderiv ℝ (dOptObj H) y) he
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hm
  have hb1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hd1)
  have hb2 := mul_le_mul_of_nonneg_left h2 hd.le
  change dOptObj H y ≤ _
  nlinarith

end DOptimalProof


namespace DOptimalProof
open RelSmoothFOM.DOptimal RelSmoothFOM.PrimalGrad

lemma uniform_barrier_linear {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : ∑ j, y j = 1) :
    fderiv ℝ logBarrier (fun _ : Fin n => 1/(n : ℝ)) (y-(fun _ => 1/(n : ℝ))) = 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [barrier_fderiv _ _ (fun _ => (one_div_pos.mpr hnR).ne')]
  change -(∑ j, (y j - 1/(n : ℝ))/(1/(n : ℝ))) = 0
  have he (j : Fin n) : (y j - 1/(n : ℝ))/(1/(n : ℝ)) = y j * n - 1 := by
    field_simp
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hy]
  simp


lemma uniform_barrier_bound {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    (hy : y ∈ posSimplex n) (δ : ℝ) (hd : 0 < δ)
    (hyl : ∀ j, δ/(n : ℝ) ≤ y j) :
    bregman logBarrier y (fun _ => 1/(n : ℝ)) ≤ (n : ℝ)*Real.log (1/δ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ j, Real.log (δ/(n : ℝ)) ≤ ∑ j, Real.log (y j) :=
    Finset.sum_le_sum fun j _ => Real.log_le_log (div_pos hd hnR) (hyl j)
  rw [bregman, uniform_barrier_linear hn y hy.2]
  simp only [logBarrier, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at *
  rw [Real.log_div hd.ne' hnR.ne'] at hsum
  simp only [one_div, Real.log_inv]
  linarith

end DOptimalProof


namespace DOptimalProof
open RelSmoothFOM.PrimalGrad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bregman_self (h : E → ℝ) (x : E) : bregman h x x = 0 := by
  simp [bregman]

lemma model_three_point {Q : Set E} (hQ : Convex ℝ Q) (f h : E → ℝ)
    {a b y : E} (hb : b ∈ Q) (hy : y ∈ Q)
    (hhd : DifferentiableAt ℝ h b)
    (hmin : ∀ u ∈ Q, f a + fderiv ℝ f a (b-a) + bregman h b a ≤
      f a + fderiv ℝ f a (u-a) + bregman h u a) :
    fderiv ℝ f a (b-y) ≤ bregman h y a - bregman h y b - bregman h b a := by
  let F : E → ℝ := fun u => f a + fderiv ℝ f a (u-a) + bregman h u a
  have hm : IsLocalMinOn F Q b := (show IsMinOn F Q b from hmin).localize
  have hd : HasFDerivAt F (fderiv ℝ f a + fderiv ℝ h b - fderiv ℝ h a) b := by
    have ha := (hasFDerivAt_id (𝕜 := ℝ) b).sub_const a
    have hfa := (fderiv ℝ f a).hasFDerivAt.comp b ha
    have hha := (fderiv ℝ h a).hasFDerivAt.comp b ha
    convert (hfa.const_add (f a)).add ((hhd.hasFDerivAt.sub_const (h a)).sub hha) using 1 <;> first | rfl | (simp only [ContinuousLinearMap.comp_id]; abel)
  have hpos := hm.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hQ.segment_subset hb hy))
  simp only [add_apply, sub_apply,
    map_sub] at hpos
  simp only [bregman, map_sub]
  linarith

lemma one_step_descent {Q : Set E} (hQ : Convex ℝ Q) (f h : E → ℝ)
    {a b y : E} (hb : b ∈ Q) (hy : y ∈ Q)
    (hhd : DifferentiableAt ℝ h b)
    (hsupport : f a + fderiv ℝ f a (y-a) ≤ f y)
    (hupper : f b ≤ f a + fderiv ℝ f a (b-a) + bregman h b a)
    (hmin : ∀ u ∈ Q, f a + fderiv ℝ f a (b-a) + bregman h b a ≤
      f a + fderiv ℝ f a (u-a) + bregman h u a) :
    f b - f y ≤ bregman h y a - bregman h y b := by
  have hh := model_three_point hQ f h hb hy hhd hmin
  simp only [map_sub] at hh hsupport hupper
  linarith

end DOptimalProof


namespace DOptimalProof
open RelSmoothFOM.PrimalGrad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma run_mem {Q : Set E} {f h : E → ℝ} {x : ℕ → E}
    (hrun : IsPrimalGradientRun Q f h 1 x) (i : ℕ) : x i ∈ Q := by
  cases i with
  | zero => exact hrun.1
  | succ i => exact (hrun.2 i).1

lemma run_monotone {Q : Set E} {f h : E → ℝ} {x : ℕ → E}
    (hrun : IsPrimalGradientRun Q f h 1 x)
    (hupper : ∀ a ∈ Q, ∀ b ∈ Q,
      f b ≤ f a + fderiv ℝ f a (b-a) + bregman h b a) :
    Antitone (fun i => f (x i)) := by
  apply antitone_nat_of_succ_le
  intro i
  have hh := hupper (x i) (run_mem hrun i) (x (i+1)) (run_mem hrun (i+1))
  have hm := (hrun.2 i).2 (x i) (run_mem hrun i)
  simp only [one_mul, sub_self, map_zero, bregman_self, add_zero] at hm
  exact hh.trans hm

lemma run_rate {Q : Set E} {f h : E → ℝ} {x : ℕ → E}
    (hQ : Convex ℝ Q) (hrun : IsPrimalGradientRun Q f h 1 x)
    (hhd : ∀ a ∈ Q, DifferentiableAt ℝ h a)
    (hsupport : ∀ a ∈ Q, ∀ b ∈ Q, f a + fderiv ℝ f a (b-a) ≤ f b)
    (hupper : ∀ a ∈ Q, ∀ b ∈ Q,
      f b ≤ f a + fderiv ℝ f a (b-a) + bregman h b a)
    (hdiv : ∀ a ∈ Q, ∀ b ∈ Q, 0 ≤ bregman h a b)
    {y : E} (hy : y ∈ Q) (k : ℕ) :
    (k : ℝ) * (f (x k) - f y) ≤ bregman h y (x 0) := by
  have hstep (i : ℕ) : f (x (i+1)) - f y ≤
      bregman h y (x i) - bregman h y (x (i+1)) := by
    apply one_step_descent hQ f h (run_mem hrun (i+1)) hy
      (hhd _ (run_mem hrun (i+1))) (hsupport _ (run_mem hrun i) _ hy)
      (hupper _ (run_mem hrun i) _ (run_mem hrun (i+1)))
    simpa only [one_mul] using (hrun.2 i).2
  have hsum : ∀ j : ℕ, (∑ i ∈ Finset.range j, (f (x (i+1)) - f y)) ≤
      bregman h y (x 0) - bregman h y (x j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have hh := hstep j
      linarith
  have ha := run_monotone hrun hupper
  have hl : (k : ℝ) * (f (x k) - f y) ≤ ∑ i ∈ Finset.range k, (f (x (i+1)) - f y) := by
    calc
      _ = ∑ _i ∈ Finset.range k, (f (x k) - f y) := by simp [mul_sub]
      _ ≤ _ := Finset.sum_le_sum fun i hi => sub_le_sub_right (ha (by simpa using Finset.mem_range.mp hi)) _
  have hn := hdiv y hy (x k) (run_mem hrun k)
  exact hl.trans ((hsum k).trans (sub_le_self _ hn))

end DOptimalProof


namespace DOptimalProof

lemma final_rate_algebra (G ε B F Y : ℝ) (n k : ℕ) (hn : 0 < n)
    (he : 0 < ε) (heG : ε ≤ G)
    (hk : 2*(n : ℝ)*Real.log (2*G/ε)/ε ≤ (k : ℝ))
    (hY : Y ≤ ε/2)
    (hF : (k : ℝ)*(F-Y) ≤ B)
    (hB : B ≤ (n : ℝ)*Real.log (2*G/ε)) : F ≤ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : 0 < G := he.trans_le heG
  have harg : 1 < 2*G/ε := (lt_div_iff₀ he).mpr (by linarith)
  have hlog : 0 < Real.log (2*G/ε) := Real.log_pos harg
  have hkR : (0 : ℝ) < k := lt_of_lt_of_le (div_pos (by positivity) he) hk
  have hb := (div_le_iff₀ he).mp hk
  have hf := hF.trans hB
  nlinarith [mul_le_mul_of_nonneg_left hY hkR.le]

end DOptimalProof


namespace DOptimalProof
open RelSmoothFOM.DOptimal RelSmoothFOM.PrimalGrad

/-- Theorem 4.1: iteration complexity for D-optimal design. -/
theorem full_native_result {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (_hH : H.rank = m) (hmn : m + 1 ≤ n)
    (x : ℕ → Fin n → ℝ) (hx0 : x 0 = fun _ => 1 / (n : ℝ))
    (hrun : RelSmoothFOM.PrimalGrad.IsPrimalGradientRun (posSimplex n) (dOptObj H) logBarrier 1 x)
    (xstar : Fin n → ℝ) (hxs : xstar ∈ stdSimplex ℝ (Fin n))
    (hxspd : (H * Matrix.diagonal xstar * H.transpose).PosDef)
    (_hopt : ∀ y ∈ stdSimplex ℝ (Fin n),
      (H * Matrix.diagonal y * H.transpose).PosDef →
        dOptObj H xstar ≤ dOptObj H y)
    (ε : ℝ) (hε : 0 < ε)
    (hεle : ε ≤ dOptObj H (x 0) - dOptObj H xstar)
    (k : ℕ)
    (hk : 2 * (n : ℝ) *
      Real.log (2 * (dOptObj H (x 0) - dOptObj H xstar) / ε) / ε ≤ (k : ℝ)) :
    dOptObj H (x k) - dOptObj H xstar ≤ ε := by
  have hn : 0 < n := by omega
  by_cases hm : m = 0
  · subst m
    have hz : dOptObj H (x 0) - dOptObj H xstar = 0 := by
      simp [dOptObj, Matrix.det_isEmpty]
    rw [hz] at hεle
    exact False.elim (not_lt_of_ge hεle hε)
  have hstar : (moment H xstar).PosDef := hxspd
  let G := dOptObj H (x 0) - dOptObj H xstar
  have hG : 0 < G := hε.trans_le hεle
  let δ := ε / (2*G)
  have hd : 0 < δ := div_pos hε (by positivity)
  have hd1 : δ ≤ 1 := (div_le_one (by positivity)).mpr (by dsimp [G]; linarith)
  let y : Fin n → ℝ := fun j => (1-δ)*xstar j + δ/n
  have hy : y ∈ posSimplex n := mixture_mem hn hxs hd hd1
  have hY := boundary_mixture_value H hn xstar hxs hstar δ hd hd1
  have hgap : dOptObj H y - dOptObj H xstar ≤ ε/2 := by
    rw [← hx0] at hY
    have he : δ*G = ε/2 := by dsimp [δ]; field_simp
    dsimp [G] at he
    change dOptObj H y ≤ _ at hY
    nlinarith
  have hrate := run_rate (posSimplex_convex n) hrun
    (fun a ha => differentiableAt_barrier a (fun j => (ha.1 j).ne'))
    (fun a ha b hb => (line_support_data H xstar hstar a b ha.1 hb.1).1)
    (fun a ha b hb => (line_support_data H xstar hstar a b ha.1 hb.1).2.1)
    (fun a ha b hb => (line_support_data H xstar hstar b a hb.1 ha.1).2.2) hy k
  have hB := uniform_barrier_bound hn y hy δ hd (fun j =>
    le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hd1) (hxs.1 j)))
  have hi : 1/δ = 2*G/ε := by dsimp [δ]; field_simp
  rw [hi, ← hx0] at hB
  apply final_rate_algebra G ε (bregman logBarrier y (x 0))
    (dOptObj H (x k)-dOptObj H xstar) (dOptObj H y-dOptObj H xstar)
    n k hn hε hεle hk hgap _ hB
  convert hrate using 1
  ring


end DOptimalProof


open RelSmoothFOM.DOptimal

namespace RelSmoothFOM.DOptimal

/-- Theorem 4.1: iteration complexity for D-optimal design. -/
theorem theorem_4_1 {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (hmn : m + 1 ≤ n)
    (x : ℕ → Fin n → ℝ) (hx0 : x 0 = fun _ => 1 / (n : ℝ))
    (hrun : RelSmoothFOM.PrimalGrad.IsPrimalGradientRun (posSimplex n) (dOptObj H) logBarrier 1 x)
    (xstar : Fin n → ℝ) (hxs : xstar ∈ stdSimplex ℝ (Fin n))
    (hxspd : (H * Matrix.diagonal xstar * H.transpose).PosDef)
    (hopt : ∀ y ∈ stdSimplex ℝ (Fin n),
      (H * Matrix.diagonal y * H.transpose).PosDef →
        dOptObj H xstar ≤ dOptObj H y)
    (ε : ℝ) (hε : 0 < ε)
    (hεle : ε ≤ dOptObj H (x 0) - dOptObj H xstar)
    (k : ℕ)
    (hk : 2 * (n : ℝ) *
      Real.log (2 * (dOptObj H (x 0) - dOptObj H xstar) / ε) / ε ≤ (k : ℝ)) :
    dOptObj H (x k) - dOptObj H xstar ≤ ε := by
  exact DOptimalProof.full_native_result H hH hmn x hx0 hrun xstar hxs hxspd hopt ε hε hεle k hk

end RelSmoothFOM.DOptimal

open RelSmoothFOM.DOptimal

theorem solution {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (hmn : m + 1 ≤ n)
    (x : ℕ → Fin n → ℝ) (hx0 : x 0 = fun _ => 1 / (n : ℝ))
    (hrun : RelSmoothFOM.PrimalGrad.IsPrimalGradientRun (posSimplex n) (dOptObj H) logBarrier 1 x)
    (xstar : Fin n → ℝ) (hxs : xstar ∈ stdSimplex ℝ (Fin n))
    (hxspd : (H * Matrix.diagonal xstar * H.transpose).PosDef)
    (hopt : ∀ y ∈ stdSimplex ℝ (Fin n),
      (H * Matrix.diagonal y * H.transpose).PosDef →
        dOptObj H xstar ≤ dOptObj H y)
    (ε : ℝ) (hε : 0 < ε)
    (hεle : ε ≤ dOptObj H (x 0) - dOptObj H xstar)
    (k : ℕ)
    (hk : 2 * (n : ℝ) *
      Real.log (2 * (dOptObj H (x 0) - dOptObj H xstar) / ε) / ε ≤ (k : ℝ)) :
    dOptObj H (x k) - dOptObj H xstar ≤ ε := RelSmoothFOM.DOptimal.theorem_4_1 H hH hmn x hx0 hrun xstar hxs hxspd hopt ε hε hεle k hk
