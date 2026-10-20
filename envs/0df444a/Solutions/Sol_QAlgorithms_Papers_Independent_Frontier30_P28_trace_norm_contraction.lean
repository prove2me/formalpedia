-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P28.trace_norm_contraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:51:18.212982+00:00
-- url     : https://prove2.me/submissions/19579248-7427-48d5-814b-812108f8c647

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28


open scoped Matrix ComplexOrder MatrixOrder

namespace G54T

section
open scoped Matrix.Norms.L2Operator

lemma unit_decomp {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) :
    ∃ (s : Finset ℂ) (P : ℂ → Matrix ι ι ℂ), (∀ z ∈ s, ‖z‖ = 1) ∧ (∀ z, (P z).PosSemidef) ∧
      ∑ z ∈ s, P z = 1 ∧ U = ∑ z ∈ s, z • P z := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hu : U ∈ unitary (Matrix ι ι ℂ) := by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]; exact ⟨hU, hU'⟩
  have hn : IsStarNormal U := ⟨by
    rw [Commute, SemiconjBy, Matrix.star_eq_conjTranspose, hU, hU']⟩
  have hfin := Matrix.finite_spectrum U
  set s := hfin.toFinset with hs
  set f : ℂ → ℂ → ℂ := fun z w => if w = z then 1 else 0 with hf
  refine ⟨s, fun z => cfc (f z) U, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hs, Set.Finite.mem_toFinset] at hz
    have := spectrum.subset_circle_of_unitary hu hz
    simpa using this
  · intro z
    show (cfc (f z) U).PosSemidef
    have h1 : cfc (f z) U = star (cfc (f z) U) * cfc (f z) U := by
      rw [← cfc_star, ← cfc_mul _ _ U (hfin.continuousOn _) (hfin.continuousOn _)]
      apply cfc_congr
      intro w _
      simp only [hf]; split_ifs <;> simp
    rw [h1, Matrix.star_eq_conjTranspose]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [← cfc_sum (fun z => f z) U s (fun i _ => hfin.continuousOn _)]
    rw [← cfc_one ℂ U]
    apply cfc_congr
    intro w hw
    have hws : w ∈ s := by rw [hs, Set.Finite.mem_toFinset]; exact hw
    simp [hf, Finset.sum_apply, Finset.sum_ite_eq, hws]
  · have : ∑ z ∈ s, z • cfc (f z) U = cfc (fun w => ∑ z ∈ s, z * f z w) U := by
      rw [show (fun w => ∑ z ∈ s, z * f z w) = ∑ z ∈ s, (fun w => z * f z w) by
        funext w; simp [Finset.sum_apply]]
      rw [cfc_sum (fun z w => z * f z w) U s (fun i _ => hfin.continuousOn _)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [cfc_const_mul z (f z) U (hfin.continuousOn _)]
    rw [this]
    conv_lhs => rw [← cfc_id' ℂ U]
    apply cfc_congr
    intro w hw
    have hws : w ∈ s := by rw [hs, Set.Finite.mem_toFinset]; exact hw
    simp [hf, Finset.sum_ite_eq, hws]

end

end G54T

lemma g53_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g53_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g53_psd_entry {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.PosSemidef) (i j : n) :
    ‖X i j‖ ^ 2 ≤ (X i i).re * (X j j).re := by
  let _ := X.toSeminormedAddCommGroup hX
  let _ := X.toInnerProductSpace hX
  have key : ∀ a b : n, (inner ℂ (Pi.single a (1:ℂ) : n → ℂ) (Pi.single b (1:ℂ))) = X a b := by
    intro a b
    show (X *ᵥ Pi.single b 1) ⬝ᵥ star (Pi.single a (1:ℂ)) = X a b
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (Pi.single i (1:ℂ) : n → ℂ) (Pi.single j (1:ℂ))
  rw [key, key, key, key] at h
  have hji : ‖X j i‖ = ‖X i j‖ := by
    rw [← hX.isHermitian.apply i j]; simp
  rw [hji, ← sq] at h
  simpa using h


open scoped InnerProductSpace

lemma g53d_sqrt_sq {n : Type} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
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

lemma g53d_sqrt_psd {n : Type} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g53d_sqrt_mul_self {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g53d_polar {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := g53d_sqrt_psd _
  have hPP : P * P = Xᴴ * X := g53d_sqrt_mul_self X
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

namespace G54T

lemma sqrt_mul_sqrt' {n : Type} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma tr_psd {n : Type} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (g53_cfc_psd Q Real.sqrt Real.sqrt_nonneg).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, sqrt_mul_sqrt' hQ, Matrix.trace_mul_comm] at h
  exact h

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma herm_pres (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hpos : ∀ X, X.PosSemidef → (T X).PosSemidef)
    {X : Matrix I I ℂ} (hX : X.IsHermitian) : (T X).IsHermitian := by
  have h := g53_parts X hX
  have h1 := hpos _ (g53_cfc_psd X (fun t => max t 0) (fun t => le_max_right _ _))
  have h2 := hpos _ (g53_cfc_psd X (fun t => max (-t) 0) (fun t => le_max_right _ _))
  rw [← h, map_sub]
  exact h1.1.sub h2.1

lemma star_pres (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hpos : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (X : Matrix I I ℂ) : T Xᴴ = (T X)ᴴ := by
  obtain ⟨H1, hH1, H2, hH2, eX⟩ : ∃ H1 : Matrix I I ℂ, H1.IsHermitian ∧ ∃ H2 : Matrix I I ℂ,
      H2.IsHermitian ∧ X = H1 + Complex.I • H2 := by
    refine ⟨(1 / 2 : ℂ) • (X + Xᴴ), ?_, (-Complex.I / 2) • (X - Xᴴ), ?_, ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
      congr 1; simp [Complex.star_def]
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
      rw [show (Xᴴ - X) = -(X - Xᴴ) by abel, smul_neg, ← neg_smul]
      congr 1; simp [Complex.star_def, Complex.conj_I]; ring
    · ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring_nf; rw [Complex.I_sq]; ring
  subst eX
  have h1 := (herm_pres T hpos hH1).eq
  have h2 := (herm_pres T hpos hH2).eq
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH1.eq, hH2.eq, map_add, map_smul,
    map_add, map_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, h1, h2]


lemma gram (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hpos : ∀ X, X.PosSemidef → (T X).PosSemidef)
    {P : Matrix J J ℂ} (hP : P.PosSemidef) (v u : I → ℂ) :
    ‖(P * T (Matrix.vecMulVec v (star u))).trace‖ ^ 2 ≤
      (P * T (Matrix.vecMulVec v (star v))).trace.re * (P * T (Matrix.vecMulVec u (star u))).trace.re := by
  set x : Fin 2 → I → ℂ := ![v, u]
  set G : Matrix (Fin 2) (Fin 2) ℂ := fun i j => (P * T (Matrix.vecMulVec (x i) (star (x j)))).trace
  have hconj : ∀ i j, G j i = star (G i j) := by
    intro i j
    simp only [G]
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hP.1.eq, ← star_pres T hpos,
      Matrix.conjTranspose_vecMulVec, star_star, Matrix.trace_mul_comm]
  have hG : G.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun a => ?_⟩
    · ext i j; rw [Matrix.conjTranspose_apply, hconj]; simp
    · set w : I → ℂ := ∑ i, star (a i) • x i
      have hw : Matrix.vecMulVec w (star w) =
          ∑ i, ∑ j, (star (a i) * a j) • Matrix.vecMulVec (x i) (star (x j)) := by
        ext p q
        simp only [w, Matrix.vecMulVec_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
          star_sum, star_mul', star_star, Matrix.sum_apply, Matrix.smul_apply]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have h0 := tr_psd hP (hpos _ (Matrix.posSemidef_vecMulVec_self_star w))
      rw [hw] at h0
      simp only [map_sum, map_smul, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
        Matrix.trace_smul, smul_eq_mul] at h0
      convert h0 using 1
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, G, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  have := g53_psd_entry hG 0 1
  simpa [G, x] using this


lemma pair_bound (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hpos : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (htp : ∀ X, (T X).trace = X.trace) {Y : Matrix J J ℂ} (hY : Yᴴ * Y = 1) (v u : I → ℂ) :
    ‖(Y * T (Matrix.vecMulVec v (star u))).trace‖ ≤
      Real.sqrt ((Matrix.vecMulVec v (star v)).trace.re) * Real.sqrt ((Matrix.vecMulVec u (star u)).trace.re) := by
  obtain ⟨s, P, hs1, hP, hsum, hYeq⟩ := unit_decomp Y hY
  set a : ℂ → ℝ := fun z => (P z * T (Matrix.vecMulVec v (star v))).trace.re
  set b : ℂ → ℝ := fun z => (P z * T (Matrix.vecMulVec u (star u))).trace.re
  have ha : ∀ z, 0 ≤ a z := fun z =>
    (Complex.nonneg_iff.mp (tr_psd (hP z) (hpos _ (Matrix.posSemidef_vecMulVec_self_star v)))).1
  have hb : ∀ z, 0 ≤ b z := fun z =>
    (Complex.nonneg_iff.mp (tr_psd (hP z) (hpos _ (Matrix.posSemidef_vecMulVec_self_star u)))).1
  have hsa : ∑ z ∈ s, a z = (Matrix.vecMulVec v (star v)).trace.re := by
    simp only [a]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hsum, Matrix.one_mul, htp]
  have hsb : ∑ z ∈ s, b z = (Matrix.vecMulVec u (star u)).trace.re := by
    simp only [b]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hsum, Matrix.one_mul, htp]
  rw [hYeq, Finset.sum_mul, Matrix.trace_sum]
  calc ‖∑ z ∈ s, ((z • P z) * T (Matrix.vecMulVec v (star u))).trace‖
      ≤ ∑ z ∈ s, ‖((z • P z) * T (Matrix.vecMulVec v (star u))).trace‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ s, Real.sqrt (a z) * Real.sqrt (b z) := by
        refine Finset.sum_le_sum fun z hz => ?_
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, norm_mul, hs1 z hz, one_mul]
        rw [← Real.sqrt_mul (ha z)]
        apply Real.le_sqrt_of_sq_le
        exact gram T hpos (hP z) v u
    _ ≤ Real.sqrt (∑ z ∈ s, a z) * Real.sqrt (∑ z ∈ s, b z) :=
        Real.sum_sqrt_mul_sqrt_le s ha hb
    _ = _ := by rw [hsa, hsb]


lemma unit_tr (x : I → ℂ) : (Matrix.vecMulVec x (star x)).trace = star x ⬝ᵥ x := by
  simp [Matrix.trace, Matrix.vecMulVec_apply, dotProduct, mul_comm]

lemma svd (A : Matrix I I ℂ) : ∃ (σ : I → ℝ) (v u : I → I → ℂ), (∀ k, 0 ≤ σ k) ∧
    (∀ k, (Matrix.vecMulVec (v k) (star (v k))).trace.re = 1) ∧
    (∀ k, (Matrix.vecMulVec (u k) (star (u k))).trace.re = 1) ∧
    A = ∑ k, (σ k : ℂ) • Matrix.vecMulVec (v k) (star (u k)) ∧
    (cfc Real.sqrt (Aᴴ * A)).trace.re = ∑ k, σ k := by
  obtain ⟨W, hW, hpol⟩ := g53d_polar A
  set Ab := cfc Real.sqrt (Aᴴ * A) with hAb
  have hAbp : Ab.PosSemidef := g53d_sqrt_psd _
  obtain ⟨Q, σ, hQQ, hσ0, hspec, htr⟩ : ∃ (Q : Matrix I I ℂ) (σ : I → ℝ), star Q * Q = 1 ∧
      (∀ k, 0 ≤ σ k) ∧ Ab = Q * Matrix.diagonal (fun k => (σ k : ℂ)) * star Q ∧
      Ab.trace.re = ∑ k, σ k := by
    have hH := hAbp.1
    refine ⟨(hH.eigenvectorUnitary : Matrix I I ℂ), hH.eigenvalues,
      Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2, hAbp.eigenvalues_nonneg, ?_, ?_⟩
    · have := hH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at this
      exact this
    · rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  set u : I → I → ℂ := fun k i => Q i k
  have hu : ∀ k, star (u k) ⬝ᵥ u k = 1 := by
    intro k
    have := congrFun (congrFun hQQ k) k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at this
    rw [← this]
    simp [dotProduct, u]
  have hAb_sum : Ab = ∑ k, (σ k : ℂ) • Matrix.vecMulVec (u k) (star (u k)) := by
    rw [hspec]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, u,
      Matrix.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  refine ⟨σ, fun k => W *ᵥ u k, u, hσ0, ?_, ?_, ?_, htr⟩
  · intro k
    rw [unit_tr, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, show star W * W = 1 from hW, Matrix.one_mulVec, hu]
    simp
  · intro k; rw [unit_tr, hu]; simp
  · rw [hpol, hAb_sum, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.mul_vecMulVec]


lemma tn_contr (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hpos : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (htp : ∀ X, (T X).trace = X.trace) (A : Matrix I I ℂ) :
    (cfc Real.sqrt ((T A)ᴴ * T A)).trace.re ≤ (cfc Real.sqrt (Aᴴ * A)).trace.re := by
  obtain ⟨W2, hW2, hpol2⟩ := g53d_polar (T A)
  have h : W2ᴴ * T A = cfc Real.sqrt ((T A)ᴴ * T A) := by
    have h0 := congrArg (fun X => W2ᴴ * X) hpol2
    rw [← Matrix.mul_assoc, hW2, Matrix.one_mul] at h0
    exact h0
  obtain ⟨σ, v, u, hσ, hv, hu, hA, htn⟩ := svd A
  rw [← h, htn]
  have hY : (W2ᴴ)ᴴ * W2ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hW2
  rw [hA, map_sum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hb := pair_bound T hpos htp hY (v k) (u k)
  rw [hv k, hu k, Real.sqrt_one, mul_one] at hb
  have := Complex.re_le_norm (W2ᴴ * T (Matrix.vecMulVec (v k) (star (u k)))).trace
  nlinarith [hσ k]

end G54T


noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- The independently established trace-norm endpoint in the proof and remark,
source PDF p.3. The pointwise accepted traceNorm interface holds for every
complex matrix, hence in particular every Hermitian matrix. This assertion
contains no semigroup or generator claim. -/
theorem solution
    (n r : ℕ) (hn : 0 < n) (hr : 0 < r) (T : Lin n r)
    (hpos : IsPositiveMap T) (htrace : TracePreserving T) :
    inducedPNorm 1 T = 1 ∧
    ∀ A : M n, QAlgorithms.traceNorm (T A) ≤ QAlgorithms.traceNorm A := by
  have hpos' : ∀ X, X.PosSemidef → (T X).PosSemidef := hpos
  have htp : ∀ X, (T X).trace = X.trace := htrace
  have hcontr : ∀ A : M n, QAlgorithms.traceNorm (T A) ≤ QAlgorithms.traceNorm A := fun A =>
    G54T.tn_contr T hpos' htp A
  have hsch : ∀ {k : ℕ} (A : M k), schattenNorm 1 A = QAlgorithms.traceNorm A := by
    intro k A
    unfold schattenNorm QAlgorithms.traceNorm
    rw [if_neg ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, div_one, Real.rpow_eq_pow, Real.rpow_one]
    congr 2
    have hnn : (0 : Matrix (Fin k) (Fin k) ℂ) ≤ Aᴴ * A :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A)
    apply cfc_congr
    intro t ht
    have := spectrum_nonneg_of_nonneg hnn ht
    simp only
    rw [Real.sqrt_eq_rpow]
  have htn_psd : ∀ {k : ℕ} {X : M k}, X.PosSemidef → QAlgorithms.traceNorm X = X.trace.re := by
    intro k X hX
    unfold QAlgorithms.traceNorm
    rw [hX.1.eq, g53d_sqrt_sq hX]
  refine ⟨?_, hcontr⟩
  unfold inducedPNorm restrictedPNorm
  apply le_antisymm
  · apply iSup_le
    rintro ⟨A, -, hA⟩
    have hA' : QAlgorithms.traceNorm A ≤ 1 := by rw [← hsch]; exact hA
    show ENNReal.ofReal (schattenNorm 1 (T A)) ≤ 1
    rw [hsch]
    calc ENNReal.ofReal (QAlgorithms.traceNorm (T A)) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal ((hcontr A).trans hA')
      _ = 1 := ENNReal.ofReal_one
  · set e : Fin n → ℂ := Pi.single ⟨0, hn⟩ 1
    set A0 : M n := Matrix.vecMulVec e (star e)
    have hA0 : A0.PosSemidef := Matrix.posSemidef_vecMulVec_self_star e
    have htr0 : A0.trace = 1 := by
      simp [A0, e, Matrix.trace, Matrix.vecMulVec_apply, Pi.single_apply]
    have hs0 : schattenNorm 1 A0 ≤ 1 := by
      rw [hsch, htn_psd hA0, htr0]; simp
    refine le_trans ?_ (le_iSup_of_le ⟨A0, trivial, hs0⟩ le_rfl)
    simp only
    rw [hsch, htn_psd (hpos' A0 hA0), htp, htr0]
    simp


end

