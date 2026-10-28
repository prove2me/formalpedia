-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.ppt_approximates_private_bits
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:26:49.278976+00:00
-- url     : https://prove2.me/submissions/5161d6bc-9054-4a41-bc6d-f6c90b37213f

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_large_corner_near_private_bit
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_hiding_ppt_region
noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

section G53D
open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
lemma p24s204_g55b_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
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

lemma p24s204_g55b_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma p24s204_g55b_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma p24s204_g55b_polar {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := p24s204_g55b_sqrt_psd _
  have hPP : P * P = Xᴴ * X := p24s204_g55b_sqrt_mul_self X
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



open scoped Matrix ComplexOrder MatrixOrder

lemma p24s204_g55bt_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma p24s204_g55bt_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma p24s204_g55bt_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : U * star U = 1)
    (hD : star U * (A - B) * U = Matrix.diagonal (RCLike.ofReal ∘ lam)) :
    ∑ i, max (lam i) 0 ≤ A.trace.re := by
  have hA' := hA.conjTranspose_mul_mul_same U
  have hB' := hB.conjTranspose_mul_mul_same U
  have htr : A.trace = (Uᴴ * A * U).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hU, one_mul]
  rw [htr, Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : (Uᴴ * A * U) i i - (Uᴴ * B * U) i i = ((lam i : ℝ) : ℂ) := by
    have := congrArg (fun M => M i i) hD
    rw [Matrix.mul_sub, Matrix.sub_mul] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have ha' : 0 ≤ ((Uᴴ * A * U) i i).re := (Complex.nonneg_iff.mp (hA'.diag_nonneg (i := i))).1
  have hb' : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.nonneg_iff.mp (hB'.diag_nonneg (i := i))).1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  simp only [Matrix.diag]
  exact max_le (by linarith) ha'

lemma p24s204_g55bt_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma p24s204_g55bt_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma p24s204_g55bt_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [p24s204_g55bt_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := p24s204_g55bt_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact p24s204_g55bt_posPart_aux lam hA hB hu hD

lemma p24s204_g55bt_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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


lemma p24s204_g55bt_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma p24s204_g55bt_tr_psd_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hs : (cfc Real.sqrt A).IsHermitian := by
    have : (cfc Real.sqrt A).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
    exact this.1
  rw [← p24s204_g55bt_sqrt_sq hA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := hB.conjTranspose_mul_mul_same (cfc Real.sqrt A)
  rw [hs.eq] at h
  have := h.trace_nonneg
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.1 this).1

lemma p24s204_g55bt_tr_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (h1 : (1 - X).PosSemidef) (h2 : (1 + X).PosSemidef) :
    (X * Y).trace.re ≤ QAlgorithms.traceNorm Y := by
  rw [p24s204_g55bt_traceNorm_herm hY]
  set P := cfc (fun t : ℝ => max t 0) Y
  set Q := cfc (fun t : ℝ => max (-t) 0) Y
  have hP : P.PosSemidef := p24s204_g55bt_cfc_psd Y _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := p24s204_g55bt_cfc_psd Y _ (fun t => le_max_right _ _)
  have hYPQ : Y = P - Q := (p24s204_g55bt_parts Y hY).symm
  have a1 := p24s204_g55bt_tr_psd_mul h1 hP
  have a2 := p24s204_g55bt_tr_psd_mul h2 hQ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at a2
  rw [hYPQ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith


end G53D

lemma p24s204_g55b_re_tr_unitary_le {H : Type*} [Fintype H] [DecidableEq H] (B Z : Matrix H H ℂ)
    (hZ : Zᴴ * Z = 1) : (Z * B).trace.re ≤ traceNorm B := by
  obtain ⟨W, hW, hB⟩ := p24s204_g55b_polar B
  set P := cfc Real.sqrt (Bᴴ * B) with hPdef
  have hP : P.PosSemidef := p24s204_g55b_sqrt_psd _
  set Y := Z * W with hYdef
  have hYY : Yᴴ * Y = 1 := by
    rw [hYdef, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Zᴴ, hZ,
      Matrix.one_mul, hW]
  set X := (1/2 : ℂ) • (Y + Yᴴ) with hX
  have e1 : 1 - X = (1/2 : ℂ) • ((1 - Y)ᴴ * (1 - Y)) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hYY, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hX]
    module
  have e2 : 1 + X = (1/2 : ℂ) • ((1 + Y)ᴴ * (1 + Y)) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, hYY, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hX]
    module
  have h1 : (1 - X).PosSemidef := by
    rw [e1]; exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (by rw [Complex.nonneg_iff]; norm_num)
  have h2 : (1 + X).PosSemidef := by
    rw [e2]; exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (by rw [Complex.nonneg_iff]; norm_num)
  have key := p24s204_g55bt_tr_le_traceNorm hP.1 h1 h2
  have hPP : traceNorm P = traceNorm B := by
    unfold traceNorm
    rw [hP.1.eq, p24s204_g55b_sqrt_sq hP]
  have hre : (X * P).trace.re = (Z * B).trace.re := by
    have hc : (Yᴴ * P).trace = star ((Y * P).trace) := by
      rw [← Matrix.trace_conjTranspose (Y * P), Matrix.conjTranspose_mul Y P, hP.1.eq, Matrix.trace_mul_comm P]
    rw [hX, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, hc, hB,
      ← Matrix.mul_assoc]
    simp only [smul_eq_mul, Complex.mul_re, Complex.add_re, Complex.star_def, Complex.conj_re,
      Complex.add_im, Complex.conj_im]
    norm_num
    ring
  rw [← hre, ← hPP]; exact key

/-! ## Kronecker-type powers -/
open scoped MatrixOrder

def p24s204_powK {ι : Type*} (n : ℕ) (M : Matrix ι ι ℂ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  fun x y => ∏ i, M (x i) (y i)

lemma p24s204_powK_mul {ι : Type*} [Fintype ι] (n : ℕ) (X Y : Matrix ι ι ℂ) :
    p24s204_powK n X * p24s204_powK n Y = p24s204_powK n (X * Y) := by
  ext x y
  simp only [p24s204_powK, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.prod_mul_distrib]

lemma p24s204_powK_trace {ι : Type*} [Fintype ι] (n : ℕ) (X : Matrix ι ι ℂ) :
    (p24s204_powK n X).trace = X.trace ^ n := by
  simp only [Matrix.trace, Matrix.diag, p24s204_powK]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : ι) => X j j)]
  simp

lemma p24s204_powK_one {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    p24s204_powK n (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  simp only [p24s204_powK, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp (fun hc => h (funext hc))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma p24s204_powK_conjTranspose {ι : Type*} (n : ℕ) (X : Matrix ι ι ℂ) :
    (p24s204_powK n X)ᴴ = p24s204_powK n Xᴴ := by
  ext x y
  simp [p24s204_powK, Matrix.conjTranspose_apply, star_prod]

lemma p24s204_powK_smul {ι : Type*} (n : ℕ) (c : ℂ) (X : Matrix ι ι ℂ) :
    p24s204_powK n (c • X) = c ^ n • p24s204_powK n X := by
  ext x y
  simp [p24s204_powK, Finset.prod_mul_distrib]

lemma p24s204_powK_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) : (p24s204_powK n M).PosSemidef := by
  set B := cfc Real.sqrt M with hB
  have hBh : Bᴴ = B := (p24s204_g55b_sqrt_psd M).1.eq
  have hBB : Bᴴ * B = M := by
    rw [hBh]
    have hnn : (0 : Matrix ι ι ℂ) ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
    rw [hB, ← cfc_mul Real.sqrt Real.sqrt M]
    conv_rhs => rw [← cfc_id ℝ M]
    apply cfc_congr
    intro t ht
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)
  let B' : Matrix (Fin n → ι) (Fin n → ι) ℂ := fun f x => ∏ i, B (f i) (x i)
  have : p24s204_powK n M = B'ᴴ * B' := by
    ext x y
    simp only [p24s204_powK, Matrix.mul_apply, Matrix.conjTranspose_apply, B', star_prod]
    rw [← hBB]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.prod_mul_distrib]
    show _ = star (∏ i, B (f i) (x i)) * ∏ i, B (f i) (y i)
    rw [star_prod]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self B'

lemma p24s204_bc_eq {I J : Type*} (X : Op (I × J)) (n : ℕ) :
    bipartiteCopies X n =
      (p24s204_powK n X).submatrix (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => I) (fun _ => J)).symm
        (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => I) (fun _ => J)).symm := by
  ext a b; rfl

lemma p24s204_bc_mul {I J : Type*} [Fintype I] [Fintype J] (X Y : Op (I × J)) (n : ℕ) :
    bipartiteCopies X n * bipartiteCopies Y n = bipartiteCopies (X * Y) n := by
  rw [p24s204_bc_eq, p24s204_bc_eq, p24s204_bc_eq, Matrix.submatrix_mul_equiv, p24s204_powK_mul]

lemma p24s204_trace_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α α ℂ)
    (e : β ≃ α) : (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => M i i)

lemma p24s204_bc_trace {I J : Type*} [Fintype I] [Fintype J] (X : Op (I × J)) (n : ℕ) :
    (bipartiteCopies X n).trace = X.trace ^ n := by
  rw [p24s204_bc_eq, p24s204_trace_submatrix_equiv, p24s204_powK_trace]

lemma p24s204_bc_conjTranspose {I J : Type*} (X : Op (I × J)) (n : ℕ) :
    (bipartiteCopies X n)ᴴ = bipartiteCopies Xᴴ n := by
  rw [p24s204_bc_eq, p24s204_bc_eq, Matrix.conjTranspose_submatrix, p24s204_powK_conjTranspose]

/-! ## Werner facts -/

abbrev p24s204_F (d : ℕ) : Op (Fin d × Fin d) :=
  QAlgorithms.Papers.Independent.Information100.P76.swapMatrix (I := Fin d)

lemma p24s204_FF (d : ℕ) : p24s204_F d * p24s204_F d = 1 := by
  ext a b
  simp only [p24s204_F, QAlgorithms.Papers.Independent.Information100.P76.swapMatrix,
    Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (a.2, a.1)]
  · obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
    by_cases h1 : a1 = b1 <;> by_cases h2 : a2 = b2 <;> simp [h1, h2, Prod.ext_iff, eq_comm]
  · intro c _ hc
    have : ¬ (a.1 = c.2 ∧ a.2 = c.1) := by
      rintro ⟨h1, h2⟩; exact hc (Prod.ext h2.symm h1.symm)
    simp [this]
  · simp

lemma p24s204_F_conj (d : ℕ) : (p24s204_F d)ᴴ = p24s204_F d := by
  ext a b
  simp only [p24s204_F, QAlgorithms.Papers.Independent.Information100.P76.swapMatrix,
    Matrix.conjTranspose_apply]
  by_cases h : b.1 = a.2 ∧ b.2 = a.1
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.symm, h'.1.symm⟩)]; simp

lemma p24s204_F_trace (d : ℕ) : (p24s204_F d).trace = d := by
  simp only [p24s204_F, QAlgorithms.Papers.Independent.Information100.P76.swapMatrix,
    Matrix.trace, Matrix.diag]
  rw [Fintype.sum_prod_type]
  have : ∀ x : Fin d, (∑ y : Fin d, if x = y ∧ y = x then (1:ℂ) else 0) = 1 := by
    intro x
    rw [Finset.sum_eq_single x] <;> simp_all [eq_comm]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma p24s204_one_trace (d : ℕ) : (1 : Op (Fin d × Fin d)).trace = (d : ℂ) ^ 2 := by
  simp [Matrix.trace_one, Fintype.card_prod, sq]

lemma p24s204_pp (d : ℕ) : (1 + p24s204_F d) * (1 + p24s204_F d) = (2 : ℂ) • (1 + p24s204_F d) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, p24s204_FF, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul]
  rw [two_smul]; abel

lemma p24s204_pm (d : ℕ) : (1 + p24s204_F d) * (1 - p24s204_F d) = 0 := by
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, p24s204_FF, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul]
  abel

def p24s204_Ps (d : ℕ) : Op (Fin d × Fin d) := (1/2 : ℂ) • (1 + p24s204_F d)

lemma p24s204_Ps_sq (d : ℕ) : p24s204_Ps d * p24s204_Ps d = p24s204_Ps d := by
  simp only [p24s204_Ps, Matrix.smul_mul, Matrix.mul_smul, p24s204_pp, smul_smul]
  congr 1; norm_num

lemma p24s204_Ps_conj (d : ℕ) : (p24s204_Ps d)ᴴ = p24s204_Ps d := by
  simp [p24s204_Ps, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, p24s204_F_conj]

lemma p24s204_sym_eq (d : ℕ) : symmetricWerner d = ((d : ℂ)^2 + d)⁻¹ • (1 + p24s204_F d) := rfl
lemma p24s204_anti_eq (d : ℕ) : antisymmetricWerner d = ((d : ℂ)^2 - d)⁻¹ • (1 - p24s204_F d) := rfl

lemma p24s204_dne (d : ℕ) (hd : 2 ≤ d) : ((d : ℂ)^2 + d) ≠ 0 ∧ ((d : ℂ)^2 - d) ≠ 0 := by
  have h1 : ((d : ℝ)^2 + d) ≠ 0 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have h2 : ((d : ℝ)^2 - d) ≠ 0 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  constructor
  · intro h; apply h1; exact_mod_cast h
  · intro h; apply h2; exact_mod_cast h

lemma p24s204_sym_trace (d : ℕ) (hd : 2 ≤ d) : (symmetricWerner d).trace = 1 := by
  rw [p24s204_sym_eq, Matrix.trace_smul, Matrix.trace_add, p24s204_F_trace, p24s204_one_trace,
    smul_eq_mul, inv_mul_cancel₀ (p24s204_dne d hd).1]

lemma p24s204_anti_trace (d : ℕ) (hd : 2 ≤ d) : (antisymmetricWerner d).trace = 1 := by
  rw [p24s204_anti_eq, Matrix.trace_smul, Matrix.trace_sub, p24s204_F_trace, p24s204_one_trace,
    smul_eq_mul, inv_mul_cancel₀ (p24s204_dne d hd).2]

lemma p24s204_Ps_sym (d : ℕ) : p24s204_Ps d * symmetricWerner d = symmetricWerner d := by
  rw [p24s204_sym_eq, p24s204_Ps, Matrix.smul_mul, Matrix.mul_smul, p24s204_pp, smul_smul, smul_smul]
  congr 1; ring

lemma p24s204_Ps_anti (d : ℕ) : p24s204_Ps d * antisymmetricWerner d = 0 := by
  rw [p24s204_anti_eq, p24s204_Ps, Matrix.smul_mul, Matrix.mul_smul, p24s204_pm, smul_zero, smul_zero]

/-! ## hiding family blocks -/

lemma p24s204_kb00 (p : ℝ) (d k : ℕ) : keyBlock (hidingFamily p d k) (0,0) (0,0) =
    ((p/2 : ℝ) : ℂ) • (hidingOne d k + hidingTwo d k) := by
  ext s t; simp [keyBlock, hidingFamily]

lemma p24s204_kb11 (p : ℝ) (d k : ℕ) : keyBlock (hidingFamily p d k) (1,1) (1,1) =
    ((p/2 : ℝ) : ℂ) • (hidingOne d k + hidingTwo d k) := by
  ext s t; simp [keyBlock, hidingFamily]

lemma p24s204_kb01 (p : ℝ) (d k : ℕ) : keyBlock (hidingFamily p d k) (0,1) (0,1) =
    ((1/2 - p : ℝ) : ℂ) • hidingTwo d k := by
  ext s t; simp [keyBlock, hidingFamily]

lemma p24s204_kb10 (p : ℝ) (d k : ℕ) : keyBlock (hidingFamily p d k) (1,0) (1,0) =
    ((1/2 - p : ℝ) : ℂ) • hidingTwo d k := by
  ext s t; simp [keyBlock, hidingFamily]

lemma p24s204_kbC (p : ℝ) (d k : ℕ) : keyBlock (hidingFamily p d k) (0,0) (1,1) =
    ((p/2 : ℝ) : ℂ) • (hidingOne d k - hidingTwo d k) := by
  ext s t; simp [keyBlock, hidingFamily]

lemma p24s204_h1_trace (d k : ℕ) (hd : 2 ≤ d) : (hidingOne d k).trace = 1 := by
  rw [hidingOne, p24s204_bc_trace, Matrix.trace_smul, Matrix.trace_add, p24s204_sym_trace d hd,
    p24s204_anti_trace d hd]
  norm_num

lemma p24s204_h2_trace (d k : ℕ) (hd : 2 ≤ d) : (hidingTwo d k).trace = 1 := by
  rw [hidingTwo, p24s204_bc_trace, p24s204_sym_trace d hd, one_pow]

/-! ## trace of the test operator against the hiding corner -/

lemma p24s204_bcP_sq (d k : ℕ) :
    bipartiteCopies (p24s204_Ps d) k * bipartiteCopies (p24s204_Ps d) k =
      bipartiteCopies (p24s204_Ps d) k := by
  rw [p24s204_bc_mul, p24s204_Ps_sq]

def p24s204_X0 (d k : ℕ) : Op ((Fin k → Fin d) × (Fin k → Fin d)) :=
  1 - (2 : ℂ) • bipartiteCopies (p24s204_Ps d) k

lemma p24s204_X0_unit (d k : ℕ) : (p24s204_X0 d k)ᴴ * p24s204_X0 d k = 1 := by
  have hc : (p24s204_X0 d k)ᴴ = p24s204_X0 d k := by
    simp only [p24s204_X0, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, p24s204_bc_conjTranspose, p24s204_Ps_conj]
    congr 1; simp
  rw [hc]
  set P := bipartiteCopies (p24s204_Ps d) k with hPdef
  have hP : P * P = P := p24s204_bcP_sq d k
  simp only [p24s204_X0, ← hPdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul]
  module

lemma p24s204_trXC (d k : ℕ) (hd : 2 ≤ d) :
    (p24s204_X0 d k * keyBlock (hidingFamily (1/3) d k) (0,0) (1,1)).trace =
      ((1/3 * (1 - (1/2 : ℝ)^k) : ℝ) : ℂ) := by
  have hs : (p24s204_Ps d * ((1/2 : ℂ) • (symmetricWerner d + antisymmetricWerner d))).trace
      = 1/2 := by
    rw [Matrix.mul_smul, Matrix.mul_add, p24s204_Ps_sym, p24s204_Ps_anti, add_zero,
      Matrix.trace_smul, p24s204_sym_trace d hd, smul_eq_mul, mul_one]
  have hs2 : (p24s204_Ps d * symmetricWerner d).trace = 1 := by
    rw [p24s204_Ps_sym, p24s204_sym_trace d hd]
  rw [p24s204_kbC, Matrix.mul_smul, Matrix.trace_smul, p24s204_X0, Matrix.sub_mul,
    Matrix.one_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.trace_sub, p24s204_h1_trace d k hd, p24s204_h2_trace d k hd]
  simp only [hidingOne, hidingTwo, p24s204_bc_mul, p24s204_bc_trace, hs, hs2, one_pow, smul_eq_mul]
  push_cast
  ring

/-! ## The construction -/

abbrev p24s204_S (d k : ℕ) := Fin k → Fin d

abbrev p24s204_N (d k n : ℕ) : ℕ := Fintype.card (Fin n → p24s204_S d k)

def p24s204_Z (n : ℕ) : ℝ := 2 * (1/3 : ℝ)^n + 2 * (1/6 : ℝ)^n

def p24s204_G (d k n : ℕ) :
    Fin (p24s204_N d k n) × Fin (p24s204_N d k n) ≃ (Fin n → p24s204_S d k × p24s204_S d k) :=
  (((Fintype.equivFin _).symm).prodCongr ((Fintype.equivFin _).symm)).trans
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => p24s204_S d k) (fun _ => p24s204_S d k)).symm

def p24s204_E (d k n : ℕ) :
    Key 2 × (Fin (p24s204_N d k n) × Fin (p24s204_N d k n)) →
      (Fin n → Key 2 × (p24s204_S d k × p24s204_S d k)) :=
  fun x i => (x.1, p24s204_G d k n x.2 i)

def p24s204_rho (d k n : ℕ) : Op (Key 2 × (Fin (p24s204_N d k n) × Fin (p24s204_N d k n))) :=
  (((p24s204_Z n)⁻¹ : ℝ) : ℂ) •
    (p24s204_powK n (hidingFamily (1/3) d k)).submatrix (p24s204_E d k n) (p24s204_E d k n)

lemma p24s204_rho_tb (d k n : ℕ) : transposeBob (p24s204_rho d k n) =
    (((p24s204_Z n)⁻¹ : ℝ) : ℂ) •
    (p24s204_powK n (transposeBob (hidingFamily (1/3) d k))).submatrix
      (p24s204_E d k n) (p24s204_E d k n) := by
  ext x y; rfl

lemma p24s204_rho_kb (d k n : ℕ) (a b : Key 2) : keyBlock (p24s204_rho d k n) a b =
    (((p24s204_Z n)⁻¹ : ℝ) : ℂ) •
    (p24s204_powK n (keyBlock (hidingFamily (1/3) d k) a b)).submatrix
      (p24s204_G d k n) (p24s204_G d k n) := by
  ext x y; rfl

lemma p24s204_Z_pos (n : ℕ) : 0 < p24s204_Z n := by
  unfold p24s204_Z; positivity

lemma p24s204_rho_trace (d k n : ℕ) (hd : 2 ≤ d) : (p24s204_rho d k n).trace = 1 := by
  have h : ∀ M : Op (Key 2 × (Fin (p24s204_N d k n) × Fin (p24s204_N d k n))),
      M.trace = ∑ a : Key 2, (keyBlock M a a).trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, keyBlock]
    rw [Fintype.sum_prod_type]
  rw [h]
  simp only [p24s204_rho_kb, Matrix.trace_smul, p24s204_trace_submatrix_equiv, p24s204_powK_trace]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, p24s204_kb00, p24s204_kb11, p24s204_kb01,
    p24s204_kb10, Matrix.trace_smul, Matrix.trace_add, p24s204_h1_trace d k hd,
    p24s204_h2_trace d k hd, smul_eq_mul]
  have hZ := (p24s204_Z_pos n).ne'
  unfold p24s204_Z at hZ ⊢
  push_cast
  field_simp
  ring_nf

/-! ## corner bound and density -/

lemma p24s204_corner (d k n : ℕ) (hd : 2 ≤ d) :
    (p24s204_Z n)⁻¹ * (1/3 * (1 - (1/2 : ℝ)^k))^n ≤
      traceNorm (keyBlock (p24s204_rho d k n) (0,0) (1,1)) := by
  set W := (p24s204_powK n (p24s204_X0 d k)).submatrix (p24s204_G d k n) (p24s204_G d k n)
  have hW : Wᴴ * W = 1 := by
    simp only [W, Matrix.conjTranspose_submatrix, p24s204_powK_conjTranspose,
      Matrix.submatrix_mul_equiv, p24s204_powK_mul, p24s204_X0_unit, p24s204_powK_one,
      Matrix.submatrix_one_equiv]
  have key := p24s204_g55b_re_tr_unitary_le (keyBlock (p24s204_rho d k n) (0,0) (1,1)) W hW
  have htr : (W * keyBlock (p24s204_rho d k n) (0,0) (1,1)).trace =
      (((p24s204_Z n)⁻¹ * (1/3 * (1 - (1/2 : ℝ)^k))^n : ℝ) : ℂ) := by
    rw [p24s204_rho_kb, Matrix.mul_smul, Matrix.trace_smul, Matrix.submatrix_mul_equiv,
      p24s204_powK_mul, p24s204_trace_submatrix_equiv, p24s204_powK_trace, p24s204_trXC d k hd]
    push_cast; rfl
  rw [htr, Complex.ofReal_re] at key
  exact key

lemma p24s204_density (d k n : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) :
    IsDensityMatrix (p24s204_rho d k n) := by
  have h0 := ((hiding_ppt_region.1 d k hd hk (1/3) (by norm_num) (by norm_num)).1).1
  refine ⟨?_, p24s204_rho_trace d k n hd⟩
  unfold p24s204_rho
  exact ((p24s204_powK_psd n h0).submatrix _).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr (p24s204_Z_pos n).le))

lemma p24s204_ppt (d k n : ℕ) (h : (transposeBob (hidingFamily (1/3) d k)).PosSemidef) :
    (transposeBob (p24s204_rho d k n)).PosSemidef := by
  rw [p24s204_rho_tb]
  exact ((p24s204_powK_psd n h).submatrix _).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr (p24s204_Z_pos n).le))

lemma p24s204_value (n k : ℕ) (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (hn : 2 / e < 2 ^ n) (hk : 2 * n / e < 2 ^ k) :
    1/2 - e < (p24s204_Z n)⁻¹ * (1/3 * (1 - (1/2 : ℝ)^k))^n := by
  set x : ℝ := (1/2)^n with hx
  set y : ℝ := (1/2)^k with hy
  have h2n : (0:ℝ) < 2^n := by positivity
  have h2k : (0:ℝ) < 2^k := by positivity
  have hx' : x * 2^n = 1 := by rw [hx, ← mul_pow]; norm_num
  have hy' : y * 2^k = 1 := by rw [hy, ← mul_pow]; norm_num
  have hx0 : 0 < x := by positivity
  have hy0 : 0 < y := by positivity
  have hxe : x < e/2 := by
    rw [div_lt_iff₀ he] at hn
    nlinarith
  have hye : n * y ≤ e/2 := by
    rw [div_lt_iff₀ he] at hk
    nlinarith
  have hy1 : y ≤ 1 := by rw [hy]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hB : 1 - n * y ≤ (1 - y)^n := by
    have := one_add_mul_le_pow (a := -y) (by linarith) n
    simpa [sub_eq_add_neg, mul_neg] using this
  have hZ : p24s204_Z n = 2 * (1/3 : ℝ)^n * (1 + x) := by
    unfold p24s204_Z; rw [hx, show (1/6 : ℝ) = 1/3 * (1/2) by norm_num, mul_pow]; ring
  have h3 : (0:ℝ) < (1/3)^n := by positivity
  have hsimp : (2 * (1/3:ℝ)^n * (1+x))⁻¹ * ((1/3)^n * (1-y)^n) = (1-y)^n / (2*(1+x)) := by
    field_simp
  rw [hZ, mul_pow, hsimp, lt_div_iff₀ (by positivity)]
  nlinarith

end QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P24
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.25, Theorem 7: shield dimensions may grow as accuracy increases. -/
theorem solution (eps : ℝ) (heps : 0 < eps) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∃ rho gamma : Op (Key 2 × (Fin a × Fin b)),
        IsDensityMatrix rho ∧ (transposeBob rho).PosSemidef ∧
        IsPrivate gamma ∧ traceNorm (rho-gamma) ≤ eps := by
  obtain ⟨hT, hLC⟩ := large_corner_near_private_bit
  have hev : {x : ℝ | privateBitError x < eps} ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    hT (gt_mem_nhds heps)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set e : ℝ := min (δ/2) (1/16) with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1/16 := min_le_right _ _
  have he2 : e ≤ δ/2 := min_le_left _ _
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / e) (by norm_num : (1:ℝ) < 2)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (2 * n / e) (by norm_num : (1:ℝ) < 2)
  set k := K + 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hk : 2 * n / e < 2 ^ k := by
    rw [hkdef, pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) K]
  obtain ⟨d, hd, hppt⟩ :=
    hiding_ppt_region.2 (1/3) (by norm_num) (by norm_num) k hk1
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hN : 0 < p24s204_N d k n := Fintype.card_pos
  have : Nonempty (Fin (p24s204_N d k n)) := ⟨⟨0, hN⟩⟩
  have hden := p24s204_density d k n hd hk1
  have hcorner : traceNorm (keyBlock (p24s204_rho d k n) (0,0) (1,1)) > 1/2 - e :=
    lt_of_lt_of_le (p24s204_value n k e he0 (by linarith) hn hk) (p24s204_corner d k n hd)
  obtain ⟨gamma, hg, hdist⟩ :=
    hLC (p24s204_rho d k n) hden e he0 (by linarith) (by convert hcorner)
  refine ⟨_, _, hN, hN, p24s204_rho d k n, gamma, hden, p24s204_ppt d k n hppt,
    by convert hg, ?_⟩
  have hdist' : traceNorm (p24s204_rho d k n - gamma) ≤ privateBitError e := by convert hdist
  refine hdist'.trans (le_of_lt ?_)
  apply hsub
  refine ⟨?_, he0⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos he0]
  linarith


end
