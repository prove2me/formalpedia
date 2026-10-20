-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.canonicalKraus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:16:30.078916+00:00
-- url     : https://prove2.me/submissions/a9f66721-2cfd-4f21-83e2-512075758081

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

open QAlgorithms.Papers.Independent.Frontier18.P17

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- rows r_a = u_a^* A -/
lemma g52_rows_gram (A : Matrix I J ℂ) (hH : (A * Aᴴ).IsHermitian) (a b : I) :
    (star ⇑(hH.eigenvectorBasis a) ᵥ* A) ⬝ᵥ star (star ⇑(hH.eigenvectorBasis b) ᵥ* A) =
      (hH.eigenvalues b : ℂ) * (star ⇑(hH.eigenvectorBasis a) ⬝ᵥ ⇑(hH.eigenvectorBasis b)) := by
  rw [Matrix.star_vecMul, star_star, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    hH.mulVec_eigenvectorBasis, dotProduct_smul, Complex.real_smul]

lemma g52_ortho (A : Matrix I J ℂ) (hH : (A * Aᴴ).IsHermitian) (a b : I) :
    star ⇑(hH.eigenvectorBasis a) ⬝ᵥ ⇑(hH.eigenvectorBasis b) = if a = b then 1 else 0 := by
  have h := hH.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at h
  have := h a b
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
  exact this

lemma g52_delta (A : Matrix I J ℂ) (hH : (A * Aᴴ).IsHermitian) (i i' : I) :
    ∑ a, (hH.eigenvectorBasis a) i * star ((hH.eigenvectorBasis a) i') = if i = i' then 1 else 0 := by
  have hU' : (hH.eigenvectorUnitary : Matrix I I ℂ) * star (hH.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (hH.eigenvectorUnitary).2
  have := congrFun (congrFun hU' i) i'
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    Matrix.one_apply] using this

lemma g52_decomp (A : Matrix I J ℂ) (hH : (A * Aᴴ).IsHermitian) (i : I) (j : J) :
    A i j = ∑ a, (hH.eigenvectorBasis a) i * (star ⇑(hH.eigenvectorBasis a) ᵥ* A) j := by
  simp only [Matrix.vecMul, dotProduct, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, g52_delta A hH]
  simp

theorem g52_thinSVD (A : Matrix I J ℂ) :
    ∃ (k : ℕ) (s : Fin k → ℝ) (u : Fin k → EuclideanSpace ℂ I) (v : Fin k → EuclideanSpace ℂ J),
      k ≤ min (Fintype.card I) (Fintype.card J) ∧ ThinSVD A s u v := by
  have hP := Matrix.posSemidef_self_mul_conjTranspose A
  set hH := hP.isHermitian with hHdef
  set μ := hH.eigenvalues with hμ
  have hμ0 : ∀ a, 0 ≤ μ a := fun a => hP.eigenvalues_nonneg a
  let r : I → J → ℂ := fun a => star ⇑(hH.eigenvectorBasis a) ᵥ* A
  have hgram : ∀ a b, r a ⬝ᵥ star (r b) = (μ b : ℂ) * (if a = b then 1 else 0) := by
    intro a b; rw [g52_rows_gram A hH a b, g52_ortho A hH a b]
  have hr0 : ∀ a, μ a = 0 → r a = 0 := by
    intro a ha
    have := hgram a a
    rw [ha] at this; simp only [Complex.ofReal_zero, zero_mul] at this
    rw [dotProduct_comm] at this
    exact dotProduct_star_self_eq_zero.mp this
  let S := {a : I // μ a ≠ 0}
  let e := Fintype.equivFin S
  have hpos : ∀ x : S, 0 < μ x.1 := fun x => lt_of_le_of_ne (hμ0 x.1) (Ne.symm x.2)
  let c : S → ℝ := fun x => Real.sqrt (μ x.1)
  have hc : ∀ x, 0 < c x := fun x => Real.sqrt_pos.mpr (hpos x)
  have hcc : ∀ x, c x * c x = μ x.1 := fun x => Real.mul_self_sqrt (hμ0 x.1)
  let u : Fin (Fintype.card S) → EuclideanSpace ℂ I := fun i => hH.eigenvectorBasis (e.symm i).1
  let v : Fin (Fintype.card S) → EuclideanSpace ℂ J := fun i =>
    WithLp.toLp 2 (((c (e.symm i))⁻¹ : ℂ) • star (r (e.symm i).1))
  have hu : Orthonormal ℂ u :=
    hH.eigenvectorBasis.orthonormal.comp _ (fun i j h => e.symm.injective (Subtype.ext h))
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [v, WithLp.ofLp_toLp, star_smul, star_star, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    rw [dotProduct_comm, hgram]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, mul_one]
      have h1 := hcc (e.symm i)
      have h2 : (c (e.symm i) : ℂ) ≠ 0 := by exact_mod_cast (hc _).ne'
      rw [← h1]; push_cast
      simp [Complex.star_def, Complex.conj_ofReal]
      field_simp
    · have : (e.symm i).1 ≠ (e.symm j).1 := fun h => hij (e.symm.injective (Subtype.ext h))
      simp [this, hij]
  refine ⟨Fintype.card S, fun i => c (e.symm i), u, v, ?_, hu, hv, fun i => hc _, ?_⟩
  · refine le_min (Fintype.card_subtype_le _) ?_
    have := hv.linearIndependent.fintype_card_le_finrank
    simpa [finrank_euclideanSpace] using this
  · ext a b
    rw [g52_decomp A hH a b, Finset.sum_apply, Finset.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, u, v, WithLp.ofLp_toLp, Pi.smul_apply, Pi.star_apply,
      star_star, smul_eq_mul]
    rw [Equiv.sum_comp e.symm (fun x : S => (c x : ℂ) * ((hH.eigenvectorBasis x.1) a *
      (starRingEnd ℂ) (((c x)⁻¹ : ℂ) * star (r x.1 b))))]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun a => μ a ≠ 0)]
    have hz : ∑ x : {a : I // ¬ μ a ≠ 0}, (hH.eigenvectorBasis x.1) a * r x.1 b = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hr0 x.1 (not_not.mp x.2)]; simp
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h2 : (c x : ℂ) ≠ 0 := by exact_mod_cast (hc x).ne'
    simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.star_def, RingHomCompTriple.comp_apply,
      RingHom.id_apply]
    show _ = (c x : ℂ) * ((hH.eigenvectorBasis x.1) a * (((c x : ℂ))⁻¹ * r x.1 b))
    field_simp
    rfl

end

lemma g52_delta' {I : Type*} [Fintype I] [DecidableEq I] {H : Matrix I I ℂ} (hH : H.IsHermitian) (i i' : I) :
    ∑ a, (hH.eigenvectorBasis a) i * star ((hH.eigenvectorBasis a) i') = if i = i' then 1 else 0 := by
  have hU' : (hH.eigenvectorUnitary : Matrix I I ℂ) * star (hH.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (hH.eigenvectorUnitary).2
  have := congrFun (congrFun hU' i) i'
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    Matrix.one_apply] using this

lemma g52_spec {I : Type*} [Fintype I] [DecidableEq I] {H : Matrix I I ℂ} (hH : H.IsHermitian) (x y : I) :
    H x y = ∑ a, (hH.eigenvalues a : ℂ) * ((hH.eigenvectorBasis a) x * star ((hH.eigenvectorBasis a) y)) := by
  have e : H x y = ∑ z, H x z * (if z = y then 1 else 0) := by simp
  rw [e]
  simp_rw [← g52_delta' hH, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hv := congrFun (hH.mulVec_eigenvectorBasis a) x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at hv
  rw [← mul_assoc]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [hv]

lemma g52_eigspec {I : Type*} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (hP : H.PosSemidef) :
    ∃ (k : ℕ) (s : Fin k → ℝ) (u : Fin k → EuclideanSpace ℂ I),
      k ≤ Fintype.card I ∧ ThinSVD H s u u := by
  set hH := hP.isHermitian
  let S := {a : I // hH.eigenvalues a ≠ 0}
  let e := Fintype.equivFin S
  have hpos : ∀ x : S, 0 < hH.eigenvalues x.1 :=
    fun x => lt_of_le_of_ne (hP.eigenvalues_nonneg x.1) (Ne.symm x.2)
  let u : Fin (Fintype.card S) → EuclideanSpace ℂ I := fun i => hH.eigenvectorBasis (e.symm i).1
  have hu : Orthonormal ℂ u :=
    hH.eigenvectorBasis.orthonormal.comp _ (fun i j h => e.symm.injective (Subtype.ext h))
  refine ⟨Fintype.card S, fun i => hH.eigenvalues (e.symm i).1, u, Fintype.card_subtype_le _, hu, hu,
    fun i => hpos _, ?_⟩
  ext x y
  rw [g52_spec hH x y, Finset.sum_apply, Finset.sum_apply]
  rw [Equiv.sum_comp e.symm (fun z : S => (((hH.eigenvalues z.1 : ℝ) : ℂ) • fun a b =>
    (hH.eigenvectorBasis z.1) a * (starRingEnd ℂ) ((hH.eigenvectorBasis z.1) b)) x y)]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => hH.eigenvalues a ≠ 0)]
  have hz : ∑ z : {a : I // ¬ hH.eigenvalues a ≠ 0}, (hH.eigenvalues z.1 : ℂ) *
      ((hH.eigenvectorBasis z.1) x * star ((hH.eigenvectorBasis z.1) y)) = 0 :=
    Finset.sum_eq_zero fun z _ => by rw [not_not.mp z.2]; simp
  rw [hz, add_zero]
  rfl

lemma g52_dyn_psd {N : ℕ} (Phi : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (hPhi : CPTP Phi) : (dynamical Phi).PosSemidef := by
  obtain ⟨hCP, -⟩ := hPhi
  let Ω : Fin N × Fin N → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hX := Matrix.posSemidef_vecMulVec_self_star Ω
  have hY := hCP N _ hX
  have hE : ∀ a a' : Fin N, (Matrix.of fun i i' => Matrix.vecMulVec Ω (star Ω) (a, i) (a', i')) =
      Matrix.single a a' 1 := by
    intro a a'
    ext i i'
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, Ω, Matrix.single_apply]
    by_cases h1 : a = i <;> by_cases h2 : a' = i' <;> simp [h1, h2]
  have hdyn : dynamical Phi = (QAlgorithms.idTensorSuperop Phi (Matrix.vecMulVec Ω (star Ω))).submatrix
      (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext p q
    simp only [dynamical, Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.fst_swap,
      Prod.snd_swap, QAlgorithms.idTensorSuperop, Matrix.of_apply]
    rw [hE]
  rw [hdyn]; exact hY.submatrix _

lemma g52_lin_expand {N : ℕ} (Phi : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (rho : Matrix (Fin N) (Fin N) ℂ) :
    Phi rho = ∑ j, ∑ j', rho j j' • Phi (Matrix.single j j' 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single rho]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

open QAlgorithms in
theorem solution {N : ℕ} (hN : 0 < N)
    (Phi : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (hPhi : CPTP Phi) :
    ∃ (k : ℕ) (s : Fin k → ℝ)
      (v : Fin k → EuclideanSpace ℂ (Fin N × Fin N)),
      k ≤ N*N ∧ ThinSVD (dynamical Phi) s v v ∧
      ∀ rho, QAlgorithms.IsDensityMatrix rho →
        Phi rho = ∑ i, (s i : ℂ) • (unres (v i) * rho * (unres (v i))ᴴ) := by
  obtain ⟨k, s, v, hk, hsvd⟩ := g52_eigspec (dynamical Phi) (g52_dyn_psd Phi hPhi)
  refine ⟨k, s, v, by simpa using hk, hsvd, fun rho _ => ?_⟩
  have hD := hsvd.2.2.2
  ext i i'
  rw [g52_lin_expand Phi rho]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, unres,
    Matrix.conjTranspose_apply]
  have key : ∀ j j', Phi (Matrix.single j j' 1) i i' =
      ∑ x, (s x : ℂ) * (v x (i, j) * star (v x (i', j'))) := by
    intro j j'
    have := congrFun (congrFun hD (i, j)) (i', j')
    simp only [dynamical] at this
    rw [this, Finset.sum_apply, Finset.sum_apply]
    rfl
  simp_rw [key, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
