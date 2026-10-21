-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.nearby_private_bit_corner
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:30:03.365328+00:00
-- url     : https://prove2.me/submissions/d26a29fe-18e8-4b48-96b1-cf4f2ed1891a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section G53D
open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
lemma g55b_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
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

lemma g55b_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g55b_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g55b_polar {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := g55b_sqrt_psd _
  have hPP : P * P = Xᴴ * X := g55b_sqrt_mul_self X
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

lemma g55bt_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g55bt_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

lemma g55bt_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
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

lemma g55bt_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g55bt_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g55bt_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [g55bt_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := g55bt_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact g55bt_posPart_aux lam hA hB hu hD

lemma g55bt_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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


lemma g55bt_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma g55bt_tr_psd_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hs : (cfc Real.sqrt A).IsHermitian := by
    have : (cfc Real.sqrt A).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
    exact this.1
  rw [← g55bt_sqrt_sq hA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := hB.conjTranspose_mul_mul_same (cfc Real.sqrt A)
  rw [hs.eq] at h
  have := h.trace_nonneg
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.1 this).1

lemma g55bt_tr_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (h1 : (1 - X).PosSemidef) (h2 : (1 + X).PosSemidef) :
    (X * Y).trace.re ≤ QAlgorithms.traceNorm Y := by
  rw [g55bt_traceNorm_herm hY]
  set P := cfc (fun t : ℝ => max t 0) Y
  set Q := cfc (fun t : ℝ => max (-t) 0) Y
  have hP : P.PosSemidef := g55bt_cfc_psd Y _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := g55bt_cfc_psd Y _ (fun t => le_max_right _ _)
  have hYPQ : Y = P - Q := (g55bt_parts Y hY).symm
  have a1 := g55bt_tr_psd_mul h1 hP
  have a2 := g55bt_tr_psd_mul h2 hQ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at a2
  rw [hYPQ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith


end G53D

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

lemma g55b_psd_trace {n : Type*} [Fintype n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    P.trace = ((P.trace.re : ℝ) : ℂ) := by
  have h := hP.trace_nonneg
  rw [Complex.nonneg_iff] at h
  apply Complex.ext <;> simp [← h.2]

lemma g55b_tn_psd {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    (traceNorm P : ℂ) = P.trace := by
  unfold traceNorm
  rw [hP.1.eq, g55b_sqrt_sq hP, ← g55b_psd_trace hP]

/-- polar: B = W P with W unitary, and traces. -/
lemma g55b_polar_tr {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (Wᴴ * B).trace = (traceNorm B : ℂ) ∧
      (Bᴴ * W).trace = (traceNorm B : ℂ) ∧ traceNorm Bᴴ = traceNorm B := by
  obtain ⟨W, hW, hB⟩ := g55b_polar B
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  set P := cfc Real.sqrt (Bᴴ * B) with hPdef
  have hP : P.PosSemidef := g55b_sqrt_psd _
  have hPh : Pᴴ = P := hP.1.eq
  have htn : (traceNorm B : ℂ) = P.trace := by
    unfold traceNorm; rw [← hPdef, ← g55b_psd_trace hP]
  have h1 : (Wᴴ * B).trace = (traceNorm B : ℂ) := by
    rw [htn, hB, ← Matrix.mul_assoc, hW, Matrix.one_mul]
  refine ⟨W, hW, hW', h1, ?_, ?_⟩
  · have : (Bᴴ * W).trace = star ((Wᴴ * B).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [this, h1]; simp
  · have hQ : (W * P * Wᴴ).PosSemidef := by
      simpa [Matrix.conjTranspose_conjTranspose] using hP.conjTranspose_mul_mul_same Wᴴ
    have hsq : (Bᴴ)ᴴ * Bᴴ = (W * P * Wᴴ) * (W * P * Wᴴ) := by
      rw [Matrix.conjTranspose_conjTranspose]
      conv_lhs => rw [hB]
      rw [Matrix.conjTranspose_mul, hPh]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
    have : traceNorm Bᴴ = (W * P * Wᴴ).trace.re := by
      unfold traceNorm; rw [hsq, g55b_sqrt_sq hQ]
    rw [this, Matrix.trace_mul_cycle, hW, Matrix.one_mul]
    have := congrArg Complex.re htn
    simpa using this.symm

lemma g55b_tw_left {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (a : Key d) (s : H) (f : Key d × H → ℂ) :
    ∑ x, twistingMatrix U (a, s) x * f x = ∑ u, (U a : Op H) s u * f (a, u) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [twistingMatrix]
  · intro k _ hk
    simp [twistingMatrix, Ne.symm hk]
  · simp

lemma g55b_tw_right {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (b : Key d) (t : H) (f : Key d × H → ℂ) :
    ∑ x, f x * star (twistingMatrix U (b, t) x) = ∑ u, f (b, u) * star ((U b : Op H) t u) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [twistingMatrix]
  · intro k _ hk
    simp [twistingMatrix, Ne.symm hk]
  · simp

lemma g55b_twist_block {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (rho : Op (Key d × H)) (a b : Key d) :
    keyBlock (twist U rho) a b = (U a : Op H) * keyBlock rho a b * (U b : Op H)ᴴ := by
  ext s t
  simp only [keyBlock, twist, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [g55b_tw_right U b t (fun x => ∑ j, twistingMatrix U (a, s) j * rho j x)]
  simp only [g55b_tw_left]

lemma g55b_traceRight_twist {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (rho : Op (Key d × H)) (a b : Key d) :
    traceRight (twist U rho) a b = ((U a : Op H) * keyBlock rho a b * (U b : Op H)ᴴ).trace := by
  rw [← g55b_twist_block]; rfl


lemma g55b_re_tr_unitary_le {H : Type*} [Fintype H] [DecidableEq H] (B Z : Matrix H H ℂ)
    (hZ : Zᴴ * Z = 1) : (Z * B).trace.re ≤ traceNorm B := by
  obtain ⟨W, hW, hB⟩ := g55b_polar B
  set P := cfc Real.sqrt (Bᴴ * B) with hPdef
  have hP : P.PosSemidef := g55b_sqrt_psd _
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
  have key := g55bt_tr_le_traceNorm hP.1 h1 h2
  have hPP : traceNorm P = traceNorm B := by
    unfold traceNorm
    rw [hP.1.eq, g55b_sqrt_sq hP]
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

lemma g55b_block_psd {H : Type*} [Fintype H] [DecidableEq H] (Z : Op H) (hZ : Zᴴ * Z = 1)
    (σ : ℝ) (hσ : σ ^ 2 = 1) :
    let Y : Op (Key 2 × H) := fun x y => if x.1 = (1,1) ∧ y.1 = (0,0) then Z x.2 y.2 else 0
    (1 + ((σ / 2 : ℝ) : ℂ) • (Y + Yᴴ)).PosSemidef := by
  intro Y
  have hZ' : Z * Zᴴ = 1 := mul_eq_one_comm.mp hZ
  have hZe : ∀ s t, ∑ u, Z s u * (starRingEnd ℂ) (Z t u) = if s = t then 1 else 0 := by
    intro s t
    have := congrFun (congrFun hZ' s) t
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  let C : Matrix (Key 2 × H) H ℂ := fun x t =>
    (if x.1 = (0,0) then (if x.2 = t then 1 else 0) else 0) +
      (σ : ℂ) * (if x.1 = (1,1) then Z x.2 t else 0)
  let D : Op (Key 2 × H) := Matrix.diagonal (fun x => if x.1 = (0,0) ∨ x.1 = (1,1) then 1 else 0)
  have hσ2 : (σ : ℂ) ^ 2 = 1 := by
    have : ((σ ^ 2 : ℝ) : ℂ) = 1 := by rw [hσ]; simp
    simpa using this
  have hσc : (σ : ℂ) * σ = 1 := by
    have : ((σ ^ 2 : ℝ) : ℂ) = 1 := by rw [hσ]; simp
    simpa [pow_two] using this
  have hCC : C * Cᴴ = D + (σ : ℂ) • (Y + Yᴴ) := by
    ext ⟨⟨a1, a2⟩, s⟩ ⟨⟨b1, b2⟩, t⟩
    rw [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.add_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    simp only [C, D, Y]
    fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
      simp [Matrix.diagonal_apply, mul_add, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hZe, Prod.ext_iff,
        mul_comm, mul_left_comm, mul_assoc, hσc] <;> ring_nf <;> (try simp [hσ2, hZe])
  let E : Op (Key 2 × H) := Matrix.diagonal (fun x => if x.1 = (0,0) ∨ x.1 = (1,1) then (1/2 : ℂ) else 1)
  have hE : E.PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro x
    split_ifs <;> rw [Complex.nonneg_iff] <;> norm_num
  have hDE : 1 - (1/2 : ℂ) • D = E := by
    ext x y
    simp only [D, E, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.diagonal_apply]
    split_ifs <;> norm_num
  have heq : 1 + ((σ / 2 : ℝ) : ℂ) • (Y + Yᴴ) = (1/2 : ℂ) • (C * Cᴴ) + (1 - (1/2 : ℂ) • D) := by
    rw [hCC]
    push_cast
    module
  rw [heq, hDE]
  exact ((Matrix.posSemidef_self_mul_conjTranspose C).smul (by rw [Complex.nonneg_iff]; norm_num)).add hE

lemma g55b_block_lower {H : Type*} [Fintype H] [DecidableEq H] (M : Op (Key 2 × H))
    (hM : M.IsHermitian) (Z : Op H) (hZ : Zᴴ * Z = 1) :
    -(traceNorm M) ≤ (Z * keyBlock M (0,0) (1,1)).trace.re := by
  have hp := g55b_block_psd Z hZ 1 (by norm_num)
  have hm := g55b_block_psd Z hZ (-1) (by norm_num)
  set Y : Op (Key 2 × H) := fun x y => if x.1 = (1,1) ∧ y.1 = (0,0) then Z x.2 y.2 else 0 with hY
  set X : Op (Key 2 × H) := -((1/2 : ℂ) • (Y + Yᴴ)) with hX
  have h1 : (1 - X).PosSemidef := by
    have e : 1 - X = 1 + (((1:ℝ) / 2 : ℝ) : ℂ) • (Y + Yᴴ) := by
      rw [hX]; push_cast; module
    rw [e]; exact hp
  have h2 : (1 + X).PosSemidef := by
    have e : 1 + X = 1 + (((-1:ℝ) / 2 : ℝ) : ℂ) • (Y + Yᴴ) := by
      rw [hX]; push_cast; module
    rw [e]; exact hm
  have key := g55bt_tr_le_traceNorm hM h1 h2
  have hc : (Yᴴ * M).trace = star ((Y * M).trace) := by
    rw [← Matrix.trace_conjTranspose (Y * M), Matrix.conjTranspose_mul Y M, hM.eq,
      Matrix.trace_mul_comm M]
  have hYM : (Y * M).trace = (Z * keyBlock M (0,0) (1,1)).trace := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single ((1,1) : Key 2)]
    · refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type,
        Finset.sum_eq_single ((0,0) : Key 2)]
      · refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [hY]; simp [keyBlock]
      · intro k _ hk
        refine Finset.sum_eq_zero (fun t _ => ?_)
        rw [hY]; simp [hk]
      · simp
    · intro k _ hk
      refine Finset.sum_eq_zero (fun s _ => ?_)
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [hY]; simp [hk]
    · simp
  have hre : (X * M).trace.re = -(Z * keyBlock M (0,0) (1,1)).trace.re := by
    rw [hX, Matrix.neg_mul, Matrix.trace_neg, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul,
      Matrix.trace_add, hc, ← hYM]
    simp only [smul_eq_mul, Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.star_def,
      Complex.conj_re, Complex.add_im, Complex.conj_im]
    norm_num
    ring
  linarith
theorem solution {S T : Type*} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] (rho gamma : Op (Key 2 × (S × T)))
    (hrho : IsDensityMatrix rho) (hgamma : IsPrivate gamma)
    (eps : ℝ) (hpos : 0 < eps) (hlt : eps < 1) (hclose : traceNorm (rho-gamma) ≤ eps) :
    traceNorm (keyBlock rho (0,0) (1,1)) ≥ 1/2-eps := by
  obtain ⟨hdens, tau, htau, U, rfl⟩ := hgamma
  set Z : Op (S × T) := (U 1 : Op (S × T)) * (U 0 : Op (S × T))ᴴ with hZdef
  have hU0 : (U 0 : Op (S × T))ᴴ * (U 0 : Op (S × T)) = 1 := Matrix.mem_unitaryGroup_iff'.mp (U 0).2
  have hU1 : (U 1 : Op (S × T))ᴴ * (U 1 : Op (S × T)) = 1 := Matrix.mem_unitaryGroup_iff'.mp (U 1).2
  have hU0' : (U 0 : Op (S × T)) * (U 0 : Op (S × T))ᴴ = 1 := mul_eq_one_comm.mp hU0
  have hZ : Zᴴ * Z = 1 := by
    rw [hZdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (U 1 : Op (S × T))ᴴ, hU1, Matrix.one_mul, hU0']
  have hBg : keyBlock (privateMatrix tau U) (0,0) (1,1) =
      (2 : ℂ)⁻¹ • ((U 0 : Op (S × T)) * tau * (U 1 : Op (S × T))ᴴ) := by
    ext s t; simp [keyBlock, privateMatrix]
  have hg : (Z * keyBlock (privateMatrix tau U) (0,0) (1,1)).trace.re = 1/2 := by
    rw [hBg, Matrix.mul_smul, Matrix.trace_smul, hZdef]
    have : ((U 1 : Op (S × T)) * (U 0 : Op (S × T))ᴴ * ((U 0 : Op (S × T)) * tau * (U 1 : Op (S × T))ᴴ)).trace
        = tau.trace := by
      rw [show (U 1 : Op (S × T)) * (U 0 : Op (S × T))ᴴ * ((U 0 : Op (S × T)) * tau * (U 1 : Op (S × T))ᴴ)
          = (U 1 : Op (S × T)) * ((U 0 : Op (S × T))ᴴ * (U 0 : Op (S × T))) * tau * (U 1 : Op (S × T))ᴴ by
          simp only [Matrix.mul_assoc], hU0, Matrix.mul_one, Matrix.trace_mul_cycle, hU1, Matrix.one_mul]
    rw [this, htau.2]; norm_num
  have hsplit : keyBlock rho (0,0) (1,1) = keyBlock (privateMatrix tau U) (0,0) (1,1) +
      keyBlock (rho - privateMatrix tau U) (0,0) (1,1) := by
    ext s t; simp [keyBlock]
  have hM : (rho - privateMatrix tau U).IsHermitian := hrho.1.1.sub hdens.1.1
  have h1 := g55b_re_tr_unitary_le (keyBlock rho (0,0) (1,1)) Z hZ
  have h2 := g55b_block_lower (rho - privateMatrix tau U) hM Z hZ
  have h3 : (Z * keyBlock rho (0,0) (1,1)).trace.re =
      1/2 + (Z * keyBlock (rho - privateMatrix tau U) (0,0) (1,1)).trace.re := by
    rw [hsplit, Matrix.mul_add, Matrix.trace_add, Complex.add_re, hg]
  linarith
end
