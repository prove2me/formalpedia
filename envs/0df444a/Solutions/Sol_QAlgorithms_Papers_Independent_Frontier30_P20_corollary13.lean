-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P20.corollary13
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:53:01.181204+00:00
-- url     : https://prove2.me/submissions/559f6cd8-9416-4fd1-8620-9bb9eb9e4d3b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Frontier30.P20
open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)
open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

namespace G55T12

/-- conjugation map ρ ↦ X ρ Xᴴ -/
def adj {d : ℕ} (X : Mat d) : Super d :=
  LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℂ X).comp (LinearMap.mulRight ℂ Xᴴ))

lemma adj_apply {d : ℕ} (X ρ : Mat d) : adj X ρ = X * ρ * Xᴴ := by
  simp [adj, mul_assoc]

lemma adj_mul {d : ℕ} (X Z : Mat d) : adj X * adj Z = adj (X * Z) := by
  ext1 ρ; simp only [ContinuousLinearMap.mul_apply, adj_apply, Matrix.conjTranspose_mul]
  simp [mul_assoc]

lemma adj_one {d : ℕ} : adj (1 : Mat d) = 1 := by
  ext1 ρ; simp [adj_apply]

lemma g55_psd_of_nonneg {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (hq : ∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ hq
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have h := hq (WithLp.ofLp v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
  have him := (Complex.nonneg_iff.mp h).2
  have e : v.ofLp ⬝ᵥ star (M *ᵥ v.ofLp) = star (star v.ofLp ⬝ᵥ M *ᵥ v.ofLp) := by
    simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  rw [e]
  apply Complex.ext <;> simp; rw [← him]; simp


lemma psd_factor {d : ℕ} (Y : Mat d) (hY : Y.PosSemidef) : ∃ B : Mat d, Y = Bᴴ * B := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  exact ⟨B, hB⟩

lemma lin_expand {d : ℕ} (A : Super d) (X : Mat d) :
    A X = ∑ i, ∑ j, X i j • A (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

lemma trace_eq {d : ℕ} (A : Super d) (ρ : Mat d) :
    (A ρ).trace = (ρ * (dualIdentity A)ᴴ).trace := by
  rw [lin_expand A ρ]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    dualIdentity, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_conj, Finset.mul_sum]


open QAlgorithms.Papers.Independent.Dependency50.P28 (Positive TP)

lemma pos_of_cone {d : ℕ} {c : Bool} {A : Super d} (h : Cone c A) : Positive A.toLinearMap := by
  cases c
  · simpa [Cone] using h
  · simp only [Cone, if_true] at h
    intro ρ hρ
    have h1 := h 1 (ρ.submatrix Prod.snd Prod.snd) (hρ.submatrix _)
    have h2 := h1.submatrix (fun i : Fin d => ((0 : Fin 1), i))
    convert h2 using 1
    ext i j
    simp [QAlgorithms.idTensorSuperop]
    rfl

lemma Y_psd {d : ℕ} {A : Super d} (h : Positive A.toLinearMap) : ((dualIdentity A)ᴴ).PosSemidef := by
  refine g55_psd_of_nonneg _ ?_
  · intro v
    have hv := (h (Matrix.vecMulVec v (star v)) (Matrix.posSemidef_vecMulVec_self_star v)).trace_nonneg
    have := trace_eq A (Matrix.vecMulVec v (star v))
    simp only [ContinuousLinearMap.coe_coe] at hv
    rw [this] at hv
    convert hv using 1
    simp [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


lemma idT_comp {d r : ℕ} (A B : Super d) (Xb : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) :
    QAlgorithms.idTensorSuperop (⇑((A * B : Super d) : Mat d →ₗ[ℂ] Mat d)) Xb =
      QAlgorithms.idTensorSuperop (⇑(A : Mat d →ₗ[ℂ] Mat d))
        (QAlgorithms.idTensorSuperop (⇑(B : Mat d →ₗ[ℂ] Mat d)) Xb) := by
  ext p q; rfl

lemma idT_adj {d r : ℕ} (X : Mat d) (Xb : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) :
    QAlgorithms.idTensorSuperop (⇑((adj X : Super d) : Mat d →ₗ[ℂ] Mat d)) Xb =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin r) (Fin r) ℂ) X * Xb *
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin r) (Fin r) ℂ) X)ᴴ := by
  ext p q
  simp only [QAlgorithms.idTensorSuperop, ContinuousLinearMap.coe_coe, adj_apply, Matrix.of_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, star_mul', apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_mul]

lemma cone_right {d : ℕ} {c : Bool} {A : Super d} (h : Cone c A) (X : Mat d) : Cone c (A * adj X) := by
  cases c
  · simp only [Cone] at h ⊢
    intro ρ hρ
    simpa [adj_apply] using h _ (hρ.mul_mul_conjTranspose_same X)
  · simp only [Cone, if_true] at h ⊢
    intro r Xb hXb
    rw [idT_comp, idT_adj]
    exact h r _ (hXb.mul_mul_conjTranspose_same _)

lemma cone_left {d : ℕ} {c : Bool} {B : Super d} (h : Cone c B) (X : Mat d) : Cone c (adj X * B) := by
  cases c
  · simp only [Cone] at h ⊢
    intro ρ hρ
    simpa [adj_apply] using (h _ hρ).mul_mul_conjTranspose_same X
  · simp only [Cone, if_true] at h ⊢
    intro r Xb hXb
    rw [idT_comp, idT_adj]
    exact (h r _ hXb).mul_mul_conjTranspose_same _


open QAlgorithms.Papers.Independent.Information100.P50 (choiMatrix)

lemma choi_right {d : ℕ} (A : Super d) (X : Mat d) :
    choiMatrix ((A * adj X : Super d) : Mat d →ₗ[ℂ] Mat d) =
      Matrix.kroneckerMap (· * ·) (1 : Mat d) Xᵀ * choiMatrix (A : Mat d →ₗ[ℂ] Mat d) *
        (Matrix.kroneckerMap (· * ·) (1 : Mat d) Xᵀ)ᴴ := by
  ext p q
  rw [choiMatrix]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.mul_apply, adj_apply]
  rw [lin_expand A]
  simp only [choiMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
  simp [Matrix.single, Finset.sum_mul, ite_and, apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma choi_left {d : ℕ} (B : Super d) (Z : Mat d) :
    choiMatrix ((adj Z * B : Super d) : Mat d →ₗ[ℂ] Mat d) =
      Matrix.kroneckerMap (· * ·) Z (1 : Mat d) * choiMatrix (B : Mat d →ₗ[ℂ] Mat d) *
        (Matrix.kroneckerMap (· * ·) Z (1 : Mat d))ᴴ := by
  ext p q
  rw [choiMatrix]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.mul_apply, adj_apply]
  simp only [choiMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, ContinuousLinearMap.coe_coe]
  simp [Finset.sum_mul, apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq]
  done


lemma kron_unit_one_left {d : ℕ} (X : Mat d) (h : X.det ≠ 0) :
    IsUnit (Matrix.kroneckerMap (· * ·) (1 : Mat d) Xᵀ).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul, Matrix.det_transpose]
  exact pow_ne_zero _ h

lemma kron_unit_one_right {d : ℕ} (Z : Mat d) (h : Z.det ≠ 0) :
    IsUnit (Matrix.kroneckerMap (· * ·) Z (1 : Mat d)).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]
  exact pow_ne_zero _ h

lemma rank_conj {n : Type*} [Fintype n] [DecidableEq n] (W C : Matrix n n ℂ) (hW : IsUnit W.det) :
    (W * C * Wᴴ).rank = C.rank := by
  have hW' : IsUnit Wᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact hW.star
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hW', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hW]

lemma kraus_right {d : ℕ} (A : Super d) (X : Mat d) (h : X.det ≠ 0) :
    krausRank (A * adj X) = krausRank A := by
  unfold krausRank jamiolkowskiState
  rw [choi_right, ← Matrix.smul_mul, ← Matrix.mul_smul, rank_conj _ _ (kron_unit_one_left X h)]

lemma kraus_left {d : ℕ} (B : Super d) (Z : Mat d) (h : Z.det ≠ 0) :
    krausRank (adj Z * B) = krausRank B := by
  unfold krausRank jamiolkowskiState
  rw [choi_left, ← Matrix.smul_mul, ← Matrix.mul_smul, rank_conj _ _ (kron_unit_one_right Z h)]

end G55T12


namespace G55C13
open G55T12 QAlgorithms.Papers.Independent.Dependency50.P28

lemma two_eq {d : ℕ} (M : Mat d) : twoSidedMap M Mᴴ = adj M := by
  ext1 ρ
  simp [twoSidedMap, QAlgorithms.Papers.Independent.Dependency50.P16.sandwich, adj_apply, Matrix.mul_assoc]

lemma quad_eq {d : ℕ} (P : Super d) (v : Fin d → ℂ) :
    star v ⬝ᵥ ((dualIdentity P)ᴴ *ᵥ v) = (P (Matrix.vecMulVec v (star v))).trace := by
  rw [trace_eq]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma normalize {d : ℕ} {c : Bool} (P Q T : Super d) (hP : Cone c P) (hQ : Cone c Q)
    (hT : InClass c T) (hprod : P * Q = T) (hinv : (dualIdentity P).det ≠ 0) :
    ∃ X Z : Mat d, X * Z = 1 ∧ Z * X = 1 ∧ InClass c (P * adj X) ∧ InClass c (adj Z * Q) := by
  have hY := Y_psd (pos_of_cone hP)
  obtain ⟨Bm, hBm⟩ := psd_factor _ hY
  have hdetY : ((dualIdentity P)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; simpa using hinv
  have hdetB : Bm.det ≠ 0 := by
    intro h0; apply hdetY; rw [hBm, Matrix.det_mul, h0, mul_zero]
  have hu : IsUnit Bm.det := isUnit_iff_ne_zero.mpr hdetB
  refine ⟨Bm⁻¹, Bm, Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu,
    ⟨cone_right hP _, ?_⟩, ⟨cone_left hQ _, ?_⟩⟩
  · intro ρ
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.mul_apply, adj_apply]
    rw [trace_eq, hBm, Matrix.mul_assoc (Bm⁻¹ * ρ), ← Matrix.mul_assoc Bm⁻¹ᴴ, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  · intro ρ
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.mul_apply, adj_apply]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← hBm, Matrix.trace_mul_comm, ← trace_eq]
    have := hT.2 ρ
    rw [← hprod] at this
    simpa using this

lemma unitary_of_tp {d : ℕ} {c : Bool} (W : Mat d) (h : InClass c (adj W)) :
    IsUnitaryConjugation (adj W) := by
  have hWW : Wᴴ * W = 1 := by
    ext i j
    have := h.2 (Matrix.single j i 1)
    simp only [ContinuousLinearMap.coe_coe, adj_apply] at this
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc] at this
    have key : ∀ X : Mat d, (X * Matrix.single j i 1).trace = X i j := by
      intro X
      simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq']
    rw [key] at this
    rw [this, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [Matrix.trace_single_eq_same]
    · rw [Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hij), if_neg hij]
  have hmem : W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    exact mul_eq_one_comm.mp hWW
  exact ⟨⟨W, hmem⟩, by rw [two_eq]⟩


lemma det_ne {d : ℕ} {c : Bool} (M : Mat d) (hM : IsUnit M) (R1 : Super d) (h1 : InClass c R1) :
    (dualIdentity (adj M * R1)).det ≠ 0 := by
  have hc := cone_left h1.1 M
  have hY := Y_psd (pos_of_cone hc)
  have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have hPD : ((dualIdentity (adj M * R1))ᴴ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hY.1 fun v hv => ?_
    rw [quad_eq]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.mul_apply, adj_apply]
    set Z := R1 (Matrix.vecMulVec v (star v)) with hZ
    have hZpsd : Z.PosSemidef := pos_of_cone h1.1 _ (Matrix.posSemidef_vecMulVec_self_star v)
    have htr : Z.trace ≠ 0 := by
      have := h1.2 (Matrix.vecMulVec v (star v))
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [← hZ] at this
      rw [this, Matrix.trace_vecMulVec, dotProduct_comm]
      exact fun h => hv (dotProduct_star_self_eq_zero.mp h)
    have hMZ : (M * Z * Mᴴ).PosSemidef := hZpsd.mul_mul_conjTranspose_same M
    refine lt_of_le_of_ne hMZ.trace_nonneg (Ne.symm fun h0 => htr ?_)
    have h00 := hMZ.trace_eq_zero_iff.mp h0
    have : Z = M⁻¹ * (M * Z * Mᴴ) * Mᴴ⁻¹ := by
      have hu' : IsUnit Mᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [this, h00]; simp
  have := hPD.det_pos.ne'
  rw [Matrix.det_conjTranspose] at this
  intro h0; apply this; rw [h0, star_zero]


lemma transfer {d : ℕ} {c : Bool} (T R : Super d) (M N : Mat d) (hM : IsUnit M) (hN : IsUnit N)
    (hT : InClass c T) (hprod : T = adj M * R * adj N) (hR : Divisible c R) : Divisible c T := by
  obtain ⟨_, R1, R2, h1, h2, h12, hn1, hn2⟩ := hR
  have huM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have huN : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN
  obtain ⟨X, Z, hXZ, hZX, hP, hQ⟩ := normalize (adj M * R1) (R2 * adj N) T (cone_left h1.1 M)
    (cone_right h2.1 N) hT (by rw [hprod, h12]; simp only [mul_assoc]) (det_ne M hM R1 h1)
  refine ⟨hT, adj M * R1 * adj X, adj Z * (R2 * adj N), hP, hQ, ?_, ?_, ?_⟩
  · rw [hprod, h12]
    simp only [mul_assoc]
    rw [← mul_assoc (adj X) (adj Z), adj_mul, hXZ, adj_one, one_mul]
  · rintro ⟨U, hU⟩
    rw [two_eq] at hU
    have e : R1 = adj (M⁻¹ * (U : Mat d) * Z) := by
      rw [← adj_mul, ← adj_mul, ← hU]
      simp only [mul_assoc]
      rw [← mul_assoc (adj M⁻¹), adj_mul, Matrix.nonsing_inv_mul _ huM, adj_one, one_mul, adj_mul, hXZ,
        adj_one, mul_one]
    apply hn1; rw [e]; exact unitary_of_tp _ (e ▸ h1)
  · rintro ⟨U, hU⟩
    rw [two_eq] at hU
    have e : R2 = adj (X * (U : Mat d) * N⁻¹) := by
      rw [← adj_mul, ← adj_mul, ← hU]
      simp only [mul_assoc]
      rw [adj_mul N, Matrix.mul_nonsing_inv _ huN, adj_one, mul_one, ← mul_assoc, adj_mul, hXZ, adj_one,
        one_mul]
    apply hn2; rw [e]; exact unitary_of_tp _ (e ▸ h2)

end G55C13

open G55T12 G55C13 in
/-- Corollary 13, PDF p.12: filtering preserves two-factor divisibility in either cone. -/
theorem solution {d : ℕ} (hd : 0 < d) (completely : Bool) (T R A B : Super d)
    (hT : InClass completely T) (hR : InClass completely R)
    (hA : FilterMap A) (hB : FilterMap B) (hprod : T = A * R * B) :
    Divisible completely T ↔ Divisible completely R := by
  obtain ⟨M, hM, rfl⟩ := hA
  obtain ⟨N, hN, rfl⟩ := hB
  rw [two_eq, two_eq] at hprod
  have huM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have huN : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN
  constructor
  · intro hTd
    refine transfer R T M⁻¹ N⁻¹ ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det M huM))
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det N huN)) hR ?_ hTd
    rw [hprod]
    simp only [mul_assoc]
    rw [← mul_assoc (adj M⁻¹) (adj M), adj_mul, Matrix.nonsing_inv_mul _ huM, adj_one, one_mul, adj_mul N,
      Matrix.mul_nonsing_inv _ huN, adj_one, mul_one]
  · exact transfer T R M N hM hN hT hprod
