-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.worstSampling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:36:08.370208+00:00
-- url     : https://prove2.me/submissions/1ddc712c-e508-43c9-8247-a0b08f20d2de

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

open scoped Kronecker

lemma p17s_of_kraus {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] {ι : Type} [Fintype ι]
    (K : ι → Matrix B A ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (E : Superop A B)
    (hE : ∀ ρ, E ρ = ∑ j, K j * ρ * (K j)ᴴ) : IsChannel E := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun t => K (e.symm t), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← hK]
    exact Equiv.sum_comp e.symm (fun j => (K j)ᴴ * K j)
  · intro ρ
    rw [hE]
    unfold krausApply
    exact (Equiv.sum_comp e.symm (fun j => K j * ρ * (K j)ᴴ)).symm

lemma p17s_idT_kraus {R I : Type} [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I] {m : ℕ}
    (A : Fin m → Matrix I I ℂ) (E : Superop I I) (hEA : ∀ ρ, E ρ = krausApply A ρ) :
    ∀ ρ, idTensorSuperop (R := R) E ρ =
      ∑ j, ((1 : Matrix R R ℂ) ⊗ₖ A j) * ρ * ((1 : Matrix R R ℂ) ⊗ₖ A j)ᴴ := by
  intro ρ
  ext p q
  simp only [idTensorSuperop, Matrix.of_apply, hEA, krausApply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  conv_rhs => rw [Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp [Finset.sum_mul]

lemma p17s_idT_channel {R I : Type} [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]
    (E : Superop I I) (hE : IsChannel E) : IsChannel (idTensorSuperop (R := R) E) := by
  obtain ⟨m, A, hA, hEA⟩ := hE
  refine p17s_of_kraus (ι := Fin m) _ ?_ _ (p17s_idT_kraus A E hEA)
  unfold IsKrausFamily at hA
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.mul_one]
  have : ∑ j, (1 : Matrix R R ℂ) ⊗ₖ ((A j)ᴴ * A j) = (1 : Matrix R R ℂ) ⊗ₖ (∑ j, (A j)ᴴ * A j) := by
    ext p q; simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
  rw [this, hA, Matrix.one_kronecker_one]

lemma p17s_density {A : Type} [Fintype A] [DecidableEq A] (Φ : Superop A A) (hΦ : IsChannel Φ)
    {ρ : Matrix A A ℂ} (hρ : IsDensityMatrix ρ) : IsDensityMatrix (Φ ρ) := by
  obtain ⟨m, K, hK, hΦK⟩ := hΦ
  rw [hΦK]
  unfold krausApply
  refine ⟨Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (K j), ?_⟩
  rw [Matrix.trace_sum]
  have : ∀ j, (K j * ρ * (K j)ᴴ).trace = ((K j)ᴴ * K j * ρ).trace := by
    intro j
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hK
  rw [hK, Matrix.one_mul, hρ.2]

lemma p17s_pure {A : Type} [Fintype A] (ψ : EuclideanSpace ℂ A) (h : ‖ψ‖ = 1) :
    IsDensityMatrix (pureDensity ψ) := by
  have e : pureDensity ψ = Matrix.vecMulVec (fun i => ψ i) (star fun i => ψ i) := by
    ext i j; simp [pureDensity, Matrix.vecMulVec_apply]
  refine ⟨by rw [e]; exact Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  have h2 : ‖ψ‖ ^ 2 = 1 := by rw [h]; norm_num
  rw [EuclideanSpace.norm_sq_eq] at h2
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, Complex.mul_conj]
  rw [← Complex.ofReal_one, ← h2, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]

lemma p17s_ket_state {A : Type} [Fintype A] [DecidableEq A] (p : A) : ‖ket p‖ = 1 := by
  simp [ket]

lemma p17s_diag {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) (a x b y : I) :
    idTensorSuperop (R := I) E (pureDensity (ket (a, x))) (b, y) (b, y) =
      if b = a then E (pureDensity (ket x)) y y else 0 := by
  simp only [idTensorSuperop, Matrix.of_apply]
  split_ifs with h
  · subst h
    congr 2
    ext i i'
    simp [pureDensity, ket, Matrix.of_apply, EuclideanSpace.single_apply]
  · have : (Matrix.of fun i i' => pureDensity (ket (a, x)) (b, i) (b, i')) = 0 := by
      ext i i'
      simp [pureDensity, ket, EuclideanSpace.single_apply, h]
    rw [this, hE]
    simp [krausApply]

/-- the stabilized output for the product input |x⟩|x⟩ -/
def p17sOut {I : Type} [Fintype I] [DecidableEq I] (E : Superop I I) (x : I) :
    Matrix (I × I) (I × I) ℂ :=
  idTensorSuperop (R := I) E (pureDensity (ket (x, x)))

lemma p17s_out_density {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : FiniteProcess I I) (ψ : EuclideanSpace ℂ (I × I)) (hψ : ‖ψ‖ = 1) :
    IsDensityMatrix (idTensorSuperop (R := I) E.val (pureDensity ψ)) :=
  p17s_density _ (p17s_idT_channel _ E.2) (p17s_pure ψ hψ)

lemma p17s_out_diag {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : FiniteProcess I I) (x b y : I) :
    (p17sOut E.val x (b, y) (b, y)).re = if b = x then basisOutputLaw E.val x y else 0 := by
  obtain ⟨m, K, hK, hEK⟩ := E.2
  unfold p17sOut
  rw [p17s_diag K _ hEK]
  split_ifs <;> simp [basisOutputLaw]

lemma p17s_td_bdd {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E F : FiniteProcess I I) :
    BddAbove (Set.range (fun ψ : ProcessPureInput (I × I) =>
      stateDistance .trace (idTensorSuperop (R := I) E.val (pureDensity ψ.val))
        (idTensorSuperop (R := I) F.val (pureDensity ψ.val)))) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨ψ, rfl⟩
  have h1 := p17s_out_density E ψ.val ψ.2
  have h2 := p17s_out_density F ψ.val ψ.2
  have := p17k_tn_le h1.1 h2.1
  rw [h1.2, h2.2] at this
  simp only [stateDistance, traceDistance]
  norm_num at this ⊢
  linarith

lemma p17s_fid_bdd {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E F : FiniteProcess I I) :
    BddBelow (Set.range (fun ψ : ProcessPureInput (I × I) =>
      fidelity (idTensorSuperop (R := I) E.val (pureDensity ψ.val))
        (idTensorSuperop (R := I) F.val (pureDensity ψ.val)))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨ψ, rfl⟩
  unfold fidelity; positivity

lemma p17s_td_le {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E F : FiniteProcess I I)
    (x : I) : traceDistance (p17sOut E.val x) (p17sOut F.val x) ≤
      stabDistance (stateDistance .trace) E.val F.val := by
  unfold stabDistance maxDistance
  exact le_csSup (p17s_td_bdd E F) ⟨⟨ket (x, x), p17s_ket_state _⟩, rfl⟩

lemma p17s_fid_ge {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E F : FiniteProcess I I)
    (x : I) : stabFidelity E.val F.val ≤ fidelity (p17sOut E.val x) (p17sOut F.val x) := by
  unfold stabFidelity minFidelity
  exact csInf_le (p17s_fid_bdd E F) ⟨⟨ket (x, x), p17s_ket_state _⟩, rfl⟩

lemma p17s_out_psd {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E : FiniteProcess I I)
    (x : I) : IsDensityMatrix (p17sOut E.val x) :=
  p17s_out_density E _ (p17s_ket_state _)

lemma p17s_law_props {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E : FiniteProcess I I)
    (x : I) : (∀ y, 0 ≤ basisOutputLaw E.val x y) ∧ ∑ y, basisOutputLaw E.val x y = 1 := by
  obtain ⟨m, K, hK, hEK⟩ := E.2
  exact ⟨p17c_law_nonneg K _ hEK x, p17c_law_sum K hK _ hEK x⟩

lemma p17s_tv {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E F : FiniteProcess I I)
    (x : I) : classicalVariation (basisOutputLaw E.val x) (basisOutputLaw F.val x) ≤
      traceDistance (p17sOut E.val x) (p17sOut F.val x) := by
  have hE := p17s_out_psd E x
  have hF := p17s_out_psd F x
  have h := p17k_diag_abs (p17sOut E.val x - p17sOut F.val x) (hE.1.1.sub hF.1.1)
  simp only [Matrix.sub_apply, Complex.sub_re] at h
  rw [Fintype.sum_prod_type] at h
  have h2 : ∑ y, |(p17sOut E.val x (x, y) (x, y)).re - (p17sOut F.val x (x, y) (x, y)).re| ≤
      ∑ b, ∑ y, |(p17sOut E.val x (b, y) (b, y)).re - (p17sOut F.val x (b, y) (b, y)).re| :=
    Finset.single_le_sum (f := fun b => ∑ y, |(p17sOut E.val x (b, y) (b, y)).re -
      (p17sOut F.val x (b, y) (b, y)).re|) (fun b _ => Finset.sum_nonneg fun y _ => abs_nonneg _)
      (Finset.mem_univ x)
  have h3 : ∀ (G : FiniteProcess I I) y, (p17sOut G.val x (x, y) (x, y)).re = basisOutputLaw G.val x y := by
    intro G y; rw [p17s_out_diag]; simp
  simp only [h3] at h2
  unfold classicalVariation traceDistance
  linarith

lemma p17s_bh {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E F : FiniteProcess I I)
    (x : I) : fidelity (p17sOut E.val x) (p17sOut F.val x) ≤
      bhattacharyya (basisOutputLaw E.val x) (basisOutputLaw F.val x) ∧
      bhattacharyya (basisOutputLaw E.val x) (basisOutputLaw F.val x) ≤ 1 := by
  have hE := p17s_out_psd E x
  have hF := p17s_out_psd F x
  obtain ⟨hE0, hE1⟩ := p17s_law_props E x
  obtain ⟨hF0, hF1⟩ := p17s_law_props F x
  have hb1 : bhattacharyya (basisOutputLaw E.val x) (basisOutputLaw F.val x) ≤ 1 :=
    p17k_bhatt_le _ _ hE0 hF0 hE1 hF1
  have h := p17k_fid_diag hE.1 hF.1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x (fun b _ hb => by
    simp [p17s_out_diag, hb]) (by simp)] at h
  simp only [p17s_out_diag, if_true] at h
  have hbh : bhattacharyya (basisOutputLaw E.val x) (basisOutputLaw F.val x) =
      ∑ y, Real.sqrt (basisOutputLaw F.val x y) * Real.sqrt (basisOutputLaw E.val x y) := by
    unfold bhattacharyya
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Real.sqrt_mul (hE0 y), mul_comm]
  rw [← hbh] at h
  have hr0 := p17k_rootFid_nonneg (p17sOut E.val x) (p17sOut F.val x)
  refine ⟨?_, hb1⟩
  unfold fidelity; nlinarith

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E F : FiniteProcess I I) :
    sSup (Set.range (fun x => classicalVariation (basisOutputLaw E.val x) (basisOutputLaw F.val x))) ≤
      stabDistance (stateDistance .trace) E.val F.val ∧
    sSup (Set.range (fun x => 1 - bhattacharyya (basisOutputLaw E.val x) (basisOutputLaw F.val x))) ≤
      stabC E.val F.val ^ 2 := by
  constructor
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨x, rfl⟩
    exact (p17s_tv E F x).trans (p17s_td_le E F x)
  · obtain ⟨x0⟩ := (inferInstance : Nonempty I)
    have hs1 : stabFidelity E.val F.val ≤ 1 :=
      (p17s_fid_ge E F x0).trans ((p17s_bh E F x0).1.trans (p17s_bh E F x0).2)
    unfold stabC
    rw [Real.sq_sqrt (by linarith)]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨x, rfl⟩
    have := (p17s_fid_ge E F x).trans (p17s_bh E F x).1
    simp only
    linarith
