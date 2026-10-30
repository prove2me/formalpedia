-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.exactIdealAverageError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:30:21.404297+00:00
-- url     : https://prove2.me/submissions/be8d1ae2-aab9-4f79-bc68-5690e23425a2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P17

open scoped ComplexOrder MatrixOrder InnerProductSpace

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

lemma p17k_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt (Q * Q) = Q := by
  have hsa : IsSelfAdjoint Q := hQ.1.isSelfAdjoint
  have h1 : Q * Q = cfc (fun t : ℝ => t * t) Q := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) Q, cfc_id' ℝ Q]
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  have : 0 ≤ t := spectrum_nonneg_of_nonneg hnn ht
  simp only [Function.comp, id]
  exact Real.sqrt_mul_self this

lemma p17k_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma p17k_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma p17k_polar {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := p17k_sqrt_psd _
  have hPP : P * P = Xᴴ * X := p17k_sqrt_mul_self X
  let a : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin P
  let b : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin X
  have hinner : ∀ v, ⟪a v, a v⟫_ℂ = ⟪b v, b v⟫_ℂ := by
    intro v
    simp only [a, b, Matrix.toEuclideanLin_apply, EuclideanSpace.inner_toLp_toLp]
    rw [dotProduct_comm, dotProduct_comm (X *ᵥ _)]
    rw [Matrix.star_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP.1.eq, hPP]
  have hnorm : ∀ v, ‖a v‖ = ‖b v‖ := by
    intro v
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ,
      hinner]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← norm_eq_zero, ← hnorm, hv, norm_zero]
  let L0 : LinearMap.range a →ₗ[ℂ] EuclideanSpace ℂ n :=
    (LinearMap.ker a).liftQ b hker ∘ₗ a.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ v, L0 ⟨a v, LinearMap.mem_range_self a v⟩ = b v := by
    intro v
    simp only [L0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range a →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        rw [hL0, ← hnorm]
        rfl }
  let E := L.extend
  have hE : ∀ v, E (a v) = b v := by
    intro v
    have := L.extend_apply ⟨a v, LinearMap.mem_range_self a v⟩
    rw [this]
    exact hL0 v
  let W : Matrix n n ℂ := fun i j => (E (EuclideanSpace.single j 1)) i
  have hWv : ∀ v : EuclideanSpace ℂ n, W *ᵥ (WithLp.ofLp v) = WithLp.ofLp (E v) := by
    intro v
    have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
      ext i; simp [EuclideanSpace.single_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    ext i
    simp [Matrix.mulVec, dotProduct, W, map_sum, map_smul, mul_comm]
  refine ⟨W, ?_, ?_⟩
  · ext i j
    have := E.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [dotProduct] at this
    simp only [Pi.star_apply] at this
    rw [show (∑ k, star (W k i) * W k j) = ∑ k, (E (EuclideanSpace.single j 1)) k *
      star ((E (EuclideanSpace.single i 1)) k) from Finset.sum_congr rfl (fun k _ => mul_comm _ _)]
    rw [this]
    simp [dotProduct, Pi.single_apply, eq_comm]
  · ext i j
    have h1 := congrFun (hWv (WithLp.toLp 2 (fun k => P k j))) i
    have h2 := hE (EuclideanSpace.single j 1)
    have h3 : a (EuclideanSpace.single j 1) = WithLp.toLp 2 (fun k => P k j) := by
      ext k; simp [a, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
    rw [h3] at h2
    rw [h2] at h1
    simp only [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct] at h1
    rw [h1]
    simp [b, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

namespace P17K

variable {n : Type*} [Fintype n] [DecidableEq n]


/-- Frobenius quadratic form. -/
noncomputable def fq (P : Matrix n n ℂ) : ℝ := (Pᴴ * P).trace.re

lemma fq_nonneg (P : Matrix n n ℂ) : 0 ≤ fq P := by
  have := (Matrix.posSemidef_conjTranspose_mul_self P).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma re_tr_swap (P Q : Matrix n n ℂ) : (Qᴴ * P).trace.re = (Pᴴ * Q).trace.re := by
  have : (Qᴴ * P).trace = star ((Pᴴ * Q).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [this]; simp

lemma cs (P Q : Matrix n n ℂ) : (Pᴴ * Q).trace.re ≤ Real.sqrt (fq P) * Real.sqrt (fq Q) := by
  have hq : ∀ t : ℝ, 0 ≤ fq Q * (t * t) + (-2 * (Pᴴ * Q).trace.re) * t + fq P := by
    intro t
    have h := fq_nonneg (P - (t : ℂ) • Q)
    unfold fq at h ⊢
    have e : (P - (t : ℂ) • Q)ᴴ * (P - (t : ℂ) • Q) =
        Pᴴ * P - (t : ℂ) • (Pᴴ * Q) - (t : ℂ) • (Qᴴ * P) + ((t : ℂ) * t) • (Qᴴ * Q) := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
      module
    rw [e] at h
    simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.sub_re, Complex.add_re,
      smul_eq_mul, Complex.re_ofReal_mul, ← Complex.ofReal_mul] at h
    rw [re_tr_swap P Q] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have h2 : ((Pᴴ * Q).trace.re) ^ 2 ≤ fq P * fq Q := by nlinarith
  calc (Pᴴ * Q).trace.re ≤ |(Pᴴ * Q).trace.re| := le_abs_self _
    _ = Real.sqrt (((Pᴴ * Q).trace.re) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (fq P * fq Q) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (fq P) * Real.sqrt (fq Q) := Real.sqrt_mul (fq_nonneg P) _


lemma sqrt_mul_sqrt {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) : cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

end P17K

open P17K in
lemma p17k_fid_part {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (P : ι → Matrix n n ℂ) (hPh : ∀ k, (P k)ᴴ = P k) (hPP : ∀ k, P k * P k = P k)
    (hsum : ∑ k, P k = 1) {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    rootFidelity ρ σ ≤
      ∑ k, Real.sqrt ((P k * σ).trace.re) * Real.sqrt ((P k * ρ).trace.re) := by
  unfold rootFidelity
  set S := cfc Real.sqrt σ with hSdef
  set R := cfc Real.sqrt ρ with hRdef
  have hSh : Sᴴ = S := (p17k_sqrt_psd σ).1
  have hRh : Rᴴ = R := (p17k_sqrt_psd ρ).1
  have hSS : S * S = σ := sqrt_mul_sqrt hσ
  have hRR : R * R = ρ := sqrt_mul_sqrt hρ
  have eA : R * σ * R = (S * R)ᴴ * (S * R) := by
    rw [Matrix.conjTranspose_mul, hRh, hSh, ← hSS]; simp only [Matrix.mul_assoc]
  rw [eA]
  obtain ⟨U, hU, hA⟩ := p17k_polar (S * R)
  set Q := cfc Real.sqrt ((S * R)ᴴ * (S * R)) with hQ
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have h1 : Q.trace = (Uᴴ * (S * R)).trace := by
    rw [hA, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have h2 : Uᴴ * (S * R) = ∑ k, (P k * S * U)ᴴ * (P k * R) := by
    have : ∀ k, (P k * S * U)ᴴ * (P k * R) = Uᴴ * S * P k * R := by
      intro k
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hPh]
      calc Uᴴ * (S * P k) * (P k * R) = Uᴴ * S * (P k * P k) * R := by
            simp only [Matrix.mul_assoc]
        _ = Uᴴ * S * P k * R := by rw [hPP]
    simp only [this]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, Matrix.mul_one, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hc := cs (P k * S * U) (P k * R)
  have e1 : fq (P k * S * U) = (P k * σ).trace.re := by
    unfold fq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hPh]
    have : Uᴴ * (S * P k) * (P k * S * U) = Uᴴ * (S * (P k * P k) * S * U) := by
      simp only [Matrix.mul_assoc]
    rw [this, hPP, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU, Matrix.mul_one,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, hSS, Matrix.trace_mul_comm]
  have e2 : fq (P k * R) = (P k * ρ).trace.re := by
    unfold fq
    rw [Matrix.conjTranspose_mul, hRh, hPh]
    have : R * P k * (P k * R) = R * (P k * P k) * R := by simp only [Matrix.mul_assoc]
    rw [this, hPP, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hRR, Matrix.trace_mul_comm]
  rw [e1, e2] at hc
  exact hc

open P17K in
lemma p17k_tn_le {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    QAlgorithms.traceNorm (A - B) ≤ A.trace.re + B.trace.re := by
  unfold QAlgorithms.traceNorm
  obtain ⟨U, hU, hX⟩ := p17k_polar (A - B)
  set Q := cfc Real.sqrt ((A - B)ᴴ * (A - B)) with hQ
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have h1 : Q.trace = (Uᴴ * (A - B)).trace := by
    rw [hX, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  set S := cfc Real.sqrt A
  set R := cfc Real.sqrt B
  have hSh : Sᴴ = S := (p17k_sqrt_psd A).1
  have hRh : Rᴴ = R := (p17k_sqrt_psd B).1
  have hSS : S * S = A := sqrt_mul_sqrt hA
  have hRR : R * R = B := sqrt_mul_sqrt hB
  have e : Uᴴ * (A - B) = (S * U)ᴴ * S + (-(R * U))ᴴ * R := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hRh,
      ← hSS, ← hRR]
    simp only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, sub_eq_add_neg, Matrix.mul_add,
      Matrix.mul_neg]
  rw [h1, e, Matrix.trace_add, Complex.add_re]
  have c1 := cs (S * U) S
  have c2 := cs (-(R * U)) R
  have f1 : fq (S * U) = A.trace.re := by
    unfold fq
    rw [Matrix.conjTranspose_mul, hSh, show Uᴴ * S * (S * U) = Uᴴ * (S * S * U) by
      simp only [Matrix.mul_assoc], hSS, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU,
      Matrix.mul_one]
  have f2 : fq (-(R * U)) = B.trace.re := by
    unfold fq
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
      Matrix.conjTranspose_mul, hRh, show Uᴴ * R * (R * U) = Uᴴ * (R * R * U) by
      simp only [Matrix.mul_assoc], hRR, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU,
      Matrix.mul_one]
  have f3 : fq S = A.trace.re := by unfold fq; rw [hSh, hSS]
  have f4 : fq R = B.trace.re := by unfold fq; rw [hRh, hRR]
  rw [f1, f3] at c1
  rw [f2, f4] at c2
  have a0 : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have b0 : 0 ≤ B.trace.re := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  rw [Real.mul_self_sqrt a0] at c1
  rw [Real.mul_self_sqrt b0] at c2
  linarith

lemma p17k_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma p17k_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma p17k_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

lemma p17k_diag_re_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) :
    0 ≤ (A i i).re :=
  (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1

/-- Σ |X_ii| ≤ ‖X‖₁ for Hermitian X. -/
lemma p17k_diag_abs {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hX : X.IsHermitian) : ∑ i, |(X i i).re| ≤ QAlgorithms.traceNorm X := by
  rw [p17k_traceNorm_herm hX]
  have hA := p17k_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hB := p17k_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have hAB := p17k_parts X hX
  set A := cfc (fun t : ℝ => max t 0) X
  set B := cfc (fun t : ℝ => max (-t) 0) X
  rw [Matrix.trace, Matrix.trace, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (X i i).re = (A i i).re - (B i i).re := by rw [← hAB]; simp
  rw [this]
  have := p17k_diag_re_nonneg hA i
  have := p17k_diag_re_nonneg hB i
  simp only [Matrix.diag]
  rw [abs_le]; constructor <;> linarith

lemma p17k_key {n : Type*} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι]
    (X : Matrix n n ℂ) (hX : X.IsHermitian) (htr : X.trace.re = 0) (g : ι → n)
    (hg : Function.Injective g) :
    -(∑ x, (X (g x) (g x)).re) ≤ 2⁻¹ * QAlgorithms.traceNorm X := by
  rw [p17k_traceNorm_herm hX]
  have hA := p17k_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hB := p17k_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have hAB := p17k_parts X hX
  set A := cfc (fun t : ℝ => max t 0) X
  set B := cfc (fun t : ℝ => max (-t) 0) X
  have htr2 : A.trace.re - B.trace.re = 0 := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, hAB, htr]
  have hsum : ∑ x, (X (g x) (g x)).re = ∑ x, (A (g x) (g x)).re - ∑ x, (B (g x) (g x)).re := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hAB]; simp
  have h1 : 0 ≤ ∑ x, (A (g x) (g x)).re :=
    Finset.sum_nonneg fun x _ => p17k_diag_re_nonneg hA _
  have h2 : ∑ x, (B (g x) (g x)).re ≤ B.trace.re := by
    rw [Matrix.trace, Complex.re_sum]
    rw [← Finset.sum_image (f := fun p => (B p p).re) (fun a _ b _ h => hg h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => p17k_diag_re_nonneg hB i)
  rw [hsum]
  linarith

lemma p17k_diag_proj {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ)
    (hd : ∀ i, d i = 0 ∨ d i = 1) :
    (Matrix.diagonal d)ᴴ = Matrix.diagonal d ∧ Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal d := by
  constructor
  · rw [Matrix.diagonal_conjTranspose]
    congr 1; funext i; rcases hd i with h | h <;> simp [h]
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i; rcases hd i with h | h <;> simp [h]

lemma p17k_diag_tr {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ) (A : Matrix n n ℂ) :
    (Matrix.diagonal d * A).trace = ∑ i, d i * A i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

lemma p17k_fid_diag {n : Type*} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    rootFidelity ρ σ ≤ ∑ i, Real.sqrt (σ i i).re * Real.sqrt (ρ i i).re := by
  have h := p17k_fid_part (fun k : n => Matrix.diagonal (fun i => if i = k then (1 : ℂ) else 0))
    (fun k => (p17k_diag_proj _ (fun i => by by_cases h : i = k <;> simp [h])).1)
    (fun k => (p17k_diag_proj _ (fun i => by by_cases h : i = k <;> simp [h])).2)
    (by
      ext i j; rw [Matrix.sum_apply]
      by_cases hij : i = j
      · subst hij; simp [Matrix.diagonal_apply]
      · simp [Matrix.diagonal_apply, hij])
    hρ hσ
  simpa [p17k_diag_tr] using h

lemma p17k_fid_bin {n : Type*} [Fintype n] [DecidableEq n] (S : n → Prop) [DecidablePred S]
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    rootFidelity ρ σ ≤
      Real.sqrt (∑ i, if S i then (σ i i).re else 0) * Real.sqrt (∑ i, if S i then (ρ i i).re else 0) +
      Real.sqrt (∑ i, if S i then 0 else (σ i i).re) * Real.sqrt (∑ i, if S i then 0 else (ρ i i).re) := by
  have h := p17k_fid_part
    (fun b : Bool => Matrix.diagonal (fun i => if decide (S i) = b then (1 : ℂ) else 0))
    (fun b => (p17k_diag_proj _ (fun i => by by_cases h : decide (S i) = b <;> simp [h])).1)
    (fun b => (p17k_diag_proj _ (fun i => by by_cases h : decide (S i) = b <;> simp [h])).2)
    (by
      ext i j; rw [Matrix.sum_apply, Fintype.sum_bool]
      by_cases hij : i = j
      · subst hij; by_cases h : S i <;> simp [Matrix.diagonal_apply, h]
      · simp [Matrix.diagonal_apply, hij])
    hρ hσ
  simp only [p17k_diag_tr, Fintype.sum_bool] at h
  convert h using 3 <;>
    · rw [Complex.re_sum]; congr 1; refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : S i <;> simp [h]

lemma p17c_choi_entry {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ)
    (p q : I × I) :
    normalizedProcessState E p q =
      (∑ j, K j p.2 p.1 * conj (K j q.2 q.1)) / (Fintype.card I : ℂ) := by
  simp only [normalizedProcessState, idTensorSuperop, Matrix.of_apply, hE, krausApply,
    pureDensity, finiteMaxEntangled]
  rw [Matrix.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp [apply_ite (starRingEnd ℂ), mul_ite, ite_mul, Finset.sum_ite_eq]
  have hd : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ^ 2 = (Fintype.card I : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have hd0 : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  rw [← hd]
  field_simp

lemma p17c_law {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ)
    (x y : I) :
    basisOutputLaw E x y = (∑ j, K j y x * conj (K j y x)).re := by
  simp only [basisOutputLaw, hE, krausApply, pureDensity, ket]
  rw [Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma p17c_law_nonneg {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ)
    (x y : I) : 0 ≤ basisOutputLaw E x y := by
  rw [p17c_law K E hE, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [Complex.mul_conj]; simp [Complex.normSq_nonneg]

lemma p17c_law_sum {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) (x : I) : ∑ y, basisOutputLaw E x y = 1 := by
  have := congrArg (fun M => M x x) hK
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply_eq] at this
  simp only [p17c_law K E hE, ← Complex.re_sum]
  rw [Finset.sum_comm]
  have e : (∑ j, ∑ b, K j b x * conj (K j b x)) = ∑ j, ∑ b, star (K j b x) * K j b x := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
    simp [mul_comm]
  rw [e, this]; simp

lemma p17c_law_le_one {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) (x y : I) : basisOutputLaw E x y ≤ 1 := by
  rw [← p17c_law_sum K hK E hE x]
  exact Finset.single_le_sum (fun z _ => p17c_law_nonneg K E hE x z) (Finset.mem_univ y)

lemma p17c_herm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  rw [p17c_choi_entry K E hE, p17c_choi_entry K E hE]
  simp [mul_comm]

lemma p17c_trace {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).trace = 1 := by
  have hd0 : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  simp only [Matrix.trace, Matrix.diag, p17c_choi_entry K E hE]
  rw [← Finset.sum_div, div_eq_one_iff_eq hd0, Fintype.sum_prod_type]
  have h1 : ∀ a : I, ∑ b : I, ∑ j, K j b a * conj (K j b a) = 1 := by
    intro a
    have := congrArg (fun M => M a a) hK
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq] at this
    rw [← this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
    simp [mul_comm]
  simp [h1]

lemma p17c_psd {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).PosSemidef := by
  have heq : normalizedProcessState E = (Fintype.card I : ℂ)⁻¹ •
      ∑ j, Matrix.vecMulVec (fun p : I × I => K j p.2 p.1) (star fun p : I × I => K j p.2 p.1) := by
    ext p q
    rw [p17c_choi_entry K E hE]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, div_eq_inv_mul]
  rw [heq]
  refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun j _ =>
    Matrix.posSemidef_vecMulVec_self_star _) ?_
  exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)

lemma p17c_diag {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) (p : I × I) :
    (normalizedProcessState E p p).re = basisOutputLaw E p.1 p.2 / Fintype.card I := by
  rw [p17c_choi_entry K E hE, p17c_law K E hE,
    show (Fintype.card I : ℂ) = ((Fintype.card I : ℝ) : ℂ) by simp, Complex.div_ofReal_re]

lemma p17k_rootFid_nonneg {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    0 ≤ rootFidelity A B := by
  unfold rootFidelity
  exact (Complex.nonneg_iff.mp (p17k_sqrt_psd _).trace_nonneg).1

/-- Bhattacharyya-type bound: Σ √(a b) ≤ 1 for probability vectors. -/
lemma p17k_bhatt_le {X : Type} [Fintype X] (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hsa : ∑ x, a x = 1) (hsb : ∑ x, b x = 1) : ∑ x, Real.sqrt (a x * b x) ≤ 1 := by
  have : ∀ x, Real.sqrt (a x * b x) ≤ (a x + b x) / 2 := by
    intro x
    rw [Real.sqrt_le_left (by linarith [ha x, hb x])]
    nlinarith [sq_nonneg (a x - b x)]
  calc ∑ x, Real.sqrt (a x * b x) ≤ ∑ x, (a x + b x) / 2 := Finset.sum_le_sum fun x _ => this x
    _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hsa, hsb]; norm_num

lemma p17c_Ssum {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) (f : I → I) :
    (∑ p : I × I, if p.2 = f p.1 then (normalizedProcessState E p p).re else 0) =
      1 - meanError E f := by
  have hd : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  simp only [p17c_diag K E hE]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold meanError
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.sum_div]
  field_simp
  ring

lemma p17c_tot {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) (S : I × I → Prop) [DecidablePred S] :
    (∑ p : I × I, if S p then 0 else (normalizedProcessState E p p).re) =
      1 - ∑ p : I × I, if S p then (normalizedProcessState E p p).re else 0 := by
  have ht : ∑ p : I × I, (normalizedProcessState E p p).re = 1 := by
    rw [← Complex.re_sum]
    change (normalizedProcessState E).trace.re = 1
    rw [p17c_trace K hK E hE]; simp
  rw [← ht, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : S p <;> simp [h]

lemma p17c_mean_nonneg {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) (f : I → I) : 0 ≤ meanError E f := by
  unfold meanError
  exact div_nonneg (Finset.sum_nonneg fun x _ => by
    linarith [p17c_law_le_one K hK E hE x (f x)]) (Nat.cast_nonneg _)

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (E F : FiniteProcess I I) (f : I → I) (h : meanError F.val f = 0) :
    meanError E.val f ≤ proDistance (stateDistance .sine) E.val F.val ^ 2 ∧
    proDistance (stateDistance .sine) E.val F.val ^ 2 = 1 - proFidelity E.val F.val := by
  obtain ⟨m, K, hK, hEK⟩ := E.2
  obtain ⟨m', L, hL, hFL⟩ := F.2
  set A := normalizedProcessState E.val with hA
  set B := normalizedProcessState F.val with hB
  have hApsd := p17c_psd K _ hEK
  have hBpsd := p17c_psd L _ hFL
  have hfb := p17k_fid_bin (fun p : I × I => p.2 = f p.1) hApsd hBpsd
  rw [p17c_tot K hK _ hEK, p17c_tot L hL _ hFL, p17c_Ssum K _ hEK, p17c_Ssum L _ hFL, h] at hfb
  have hm0 := p17c_mean_nonneg K hK _ hEK f
  have hr0 := p17k_rootFid_nonneg A B
  simp only [sub_zero, Real.sqrt_one, one_mul, sub_self, Real.sqrt_zero, zero_mul, add_zero] at hfb
  have hF : proFidelity E.val F.val ≤ 1 - meanError E.val f := by
    change rootFidelity A B ^ 2 ≤ _
    have : Real.sqrt (1 - meanError E.val f) ^ 2 = 1 - meanError E.val f := by
      rw [Real.sq_sqrt (by
        unfold meanError
        have := p17c_Ssum K _ hEK f
        have hs : 0 ≤ ∑ p : I × I, if p.2 = f p.1 then (A p p).re else 0 :=
          Finset.sum_nonneg fun p _ => by
            split_ifs
            · exact p17k_diag_re_nonneg hApsd p
            · exact le_refl _
        unfold meanError at this; linarith)]
    rw [← this]
    exact pow_le_pow_left₀ hr0 hfb 2
  have h2 : proDistance (stateDistance .sine) E.val F.val ^ 2 = 1 - proFidelity E.val F.val := by
    change Real.sqrt (1 - proFidelity E.val F.val) ^ 2 = _
    rw [Real.sq_sqrt (by linarith)]
  exact ⟨by rw [h2]; linarith, h2⟩
