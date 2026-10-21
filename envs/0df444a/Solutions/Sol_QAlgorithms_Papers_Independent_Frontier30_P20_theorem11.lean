-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P20.theorem11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:08:29.683537+00:00
-- url     : https://prove2.me/submissions/aaf0e414-73f0-4342-853a-db4a5116f4c0

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


namespace G55T11
open G55T12 G55C13 QAlgorithms.Papers.Independent.Dependency50.P28
open QAlgorithms.Papers.Independent.Information100.P50 (choiMatrix)

/-- depolarizing-type map ρ ↦ (1-p) ρ + (p/d) tr ρ • 1 -/
def dep (d : ℕ) (p : ℝ) : Super d :=
  LinearMap.toContinuousLinearMap
    (((1 - p : ℝ) : ℂ) • LinearMap.id +
      (((p / d : ℝ) : ℂ) • (LinearMap.smulRight (Matrix.traceLinearMap (Fin d) ℂ ℂ) (1 : Mat d))))

lemma dep_apply (d : ℕ) (p : ℝ) (ρ : Mat d) :
    dep d p ρ = ((1 - p : ℝ) : ℂ) • ρ + (((p / d : ℝ) : ℂ) * ρ.trace) • (1 : Mat d) := by
  simp [dep, mul_smul]

lemma dep_mul (d : ℕ) (hd : 0 < d) (p q : ℝ) : dep d p * dep d q = dep d (p + q - p * q) := by
  ext1 ρ
  simp only [ContinuousLinearMap.mul_apply, dep_apply, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

lemma dep_zero (d : ℕ) : dep d 0 = 1 := by
  ext1 ρ; simp [dep_apply]

lemma dep_tp (d : ℕ) (hd : 0 < d) (p : ℝ) (ρ : Mat d) : (dep d p ρ).trace = ρ.trace := by
  rw [dep_apply, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [smul_eq_mul]
  push_cast
  field_simp
  ring


theorem g_lin_expand {I O : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g_sum_psd {I ι : Type*} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem cp_of_choi {d : ℕ} (M : Mat d →ₗ[ℂ] Mat d) (hC : (choiMatrix M).PosSemidef) :
    QAlgorithms.Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    rw [show M (Matrix.single i j 1) o o' = choiMatrix M (o, i) (o', j) from rfl, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × Fin d → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : QAlgorithms.idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g_lin_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g_sum_psd _ _ fun a => g_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem choi_of_cp {d : ℕ} (M : Mat d →ₗ[ℂ] Mat d) (h : QAlgorithms.Entanglement.IsCompletelyPositive M) :
    (choiMatrix M).PosSemidef := by
  let e := Fintype.equivFin (Fin d)
  let Ω : Fin (Fintype.card (Fin d)) × Fin d → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : choiMatrix M = (QAlgorithms.idTensorSuperop M (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : Fin d × Fin d => (e q.2, q.1)) (fun q => (e q.2, q.1)) := by
    ext ⟨o, i⟩ ⟨o', i'⟩
    rw [Matrix.submatrix_apply]
    show M (Matrix.single i i' 1) o o' =
      M (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _


lemma tr_single {d : ℕ} (i j : Fin d) : (Matrix.single i j (1 : ℂ)).trace = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [Matrix.trace_single_eq_same]
  · rw [Matrix.trace_single_eq_of_ne _ _ _ h, if_neg h]

lemma choi_dep (d : ℕ) (p : ℝ) :
    choiMatrix (dep d p : Mat d →ₗ[ℂ] Mat d) =
      ((1 - p : ℝ) : ℂ) • Matrix.vecMulVec (fun q : Fin d × Fin d => if q.1 = q.2 then (1 : ℂ) else 0)
        (star (fun q : Fin d × Fin d => if q.1 = q.2 then (1 : ℂ) else 0)) + ((p / d : ℝ) : ℂ) • 1 := by
  ext ⟨o, i⟩ ⟨o', j⟩
  simp only [choiMatrix, ContinuousLinearMap.coe_coe, dep_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.single_apply, Matrix.one_apply, tr_single,
    Prod.mk.injEq]
  by_cases h1 : i = o <;> by_cases h2 : j = o' <;> by_cases h3 : o = o' <;> by_cases h4 : i = j <;>
    simp_all <;> (try intro h) <;> (try subst h) <;> simp_all


lemma choi_A {d : ℕ} (T : Super d) (q : ℝ) :
    choiMatrix ((T * dep d q : Super d) : Mat d →ₗ[ℂ] Mat d) =
      ((1 - q : ℝ) : ℂ) • choiMatrix (T : Mat d →ₗ[ℂ] Mat d) +
        ((q / d : ℝ) : ℂ) • Matrix.kroneckerMap (· * ·) (T 1) (1 : Mat d) := by
  ext ⟨o, i⟩ ⟨o', j⟩
  simp only [choiMatrix, ContinuousLinearMap.coe_coe, ContinuousLinearMap.mul_apply, dep_apply, map_add,
    map_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, tr_single, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  by_cases h : i = j <;> simp [h]


section margin
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma psd_le_norm {n : Type} [Fintype n] [DecidableEq n] (K : Matrix n n ℂ) (hK : K.PosSemidef) :
    (((‖K‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ) - K).PosSemidef := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self (a := K) hK.1.isSelfAdjoint
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
  simpa [Complex.coe_smul] using h

lemma pd_margin {n : Type} [Fintype n] [DecidableEq n] (J K : Matrix n n ℂ) (hJ : J.PosSemidef)
    (hdet : J.det ≠ 0) (hK : K.PosSemidef) :
    ∃ ε > 0, ∀ s : ℝ, 0 ≤ s → s ≤ ε → (J - (s : ℂ) • K).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hJ.nonneg
  have hBd : B.det ≠ 0 := by
    intro h0; apply hdet; rw [hB, Matrix.star_eq_conjTranspose, Matrix.det_mul, h0, mul_zero]
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBd
  set K' := (B⁻¹)ᴴ * K * B⁻¹ with hK'
  have hK'p : K'.PosSemidef := hK.conjTranspose_mul_mul_same _
  refine ⟨1 / (‖K'‖ + 1), by positivity, fun s hs0 hs1 => ?_⟩
  have hnorm : s * ‖K'‖ ≤ 1 := by
    have h1 : s * ‖K'‖ ≤ ‖K'‖ / (‖K'‖ + 1) := by
      rw [div_eq_mul_one_div, mul_comm (‖K'‖)]
      exact mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
    have h2 : ‖K'‖ / (‖K'‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hinner : ((1 : Matrix n n ℂ) - (s : ℂ) • K').PosSemidef := by
    have e : (1 : Matrix n n ℂ) - (s : ℂ) • K' =
        (((1 - s * ‖K'‖ : ℝ)) : ℂ) • (1 : Matrix n n ℂ) +
          (s : ℂ) • ((((‖K'‖ : ℝ) : ℂ)) • (1 : Matrix n n ℂ) - K') := by
      rw [smul_sub, smul_smul]
      push_cast
      rw [sub_smul, one_smul]
      abel
    rw [e]
    refine Matrix.PosSemidef.add (Matrix.PosSemidef.one.smul ?_) ((psd_le_norm K' hK'p).smul ?_)
    · exact_mod_cast (sub_nonneg.mpr hnorm)
    · exact_mod_cast hs0
  have := hinner.conjTranspose_mul_mul_same B
  convert this using 1
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hB,
    Matrix.star_eq_conjTranspose, hK']
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hu,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

end margin


lemma det_of_rank {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (h : M.rank = Fintype.card n) :
    M.det ≠ 0 := by
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]; exact h
  have hsurj : Function.Surjective M.mulVecLin := LinearMap.range_eq_top.mp htop
  have hinj : Function.Injective M.mulVecLin := LinearMap.injective_iff_surjective.mpr hsurj
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv
  apply hinj
  simpa using hMv

lemma rank_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (hc : c ≠ 0) (M : Matrix n n ℂ) :
    (c • M).rank = M.rank := by
  rw [show c • M = (c • (1 : Matrix n n ℂ)) * M by rw [Matrix.smul_mul, Matrix.one_mul]]
  apply Matrix.rank_mul_eq_right_of_isUnit_det
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero.mpr hc).pow _

lemma purity_adj {d : ℕ} (U : Mat d) (hU : Uᴴ * U = 1) (X : Mat d) :
    ((adj U X) * (adj U X)).trace = (X * X).trace := by
  rw [adj_apply]
  calc (U * X * Uᴴ * (U * X * Uᴴ)).trace = ((U * X) * (Uᴴ * U) * X * Uᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (X * X * (Uᴴ * U)).trace := by
        rw [hU, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul,
          Matrix.mul_assoc, Matrix.mul_one]
    _ = (X * X).trace := by rw [hU, Matrix.mul_one]

lemma purity_dep {d : ℕ} (hd : 0 < d) (p : ℝ) (e : Fin d) :
    ((dep d p (Matrix.single e e 1)) * (dep d p (Matrix.single e e 1))).trace =
      ((1 - (1 - 1 / (d : ℝ)) * (p * (2 - p)) : ℝ) : ℂ) := by
  rw [dep_apply, tr_single, if_pos rfl]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.single_mul_single_same,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    Matrix.trace_single_eq_same, smul_eq_mul, mul_one]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp
  ring


lemma not_unit_dep {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ IsUnitaryConjugation (dep d p) := by
  rintro ⟨U, hU⟩
  rw [two_eq] at hU
  have hUU : (U : Mat d)ᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h1 := purity_dep (by omega) p (⟨0, by omega⟩ : Fin d)
  rw [hU, purity_adj _ hUU, Matrix.single_mul_single_same, mul_one, tr_single, if_pos rfl] at h1
  have h2 : (1 : ℝ) = 1 - (1 - 1 / (d : ℝ)) * (p * (2 - p)) := by exact_mod_cast h1
  have hs : 0 < 1 - 1 / (d : ℝ) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have : 0 < (1 - 1 / (d : ℝ)) * (p * (2 - p)) := mul_pos hs (mul_pos hp0 (by linarith))
  linarith

def qf (p : ℝ) : ℝ := -p / (1 - p)

lemma dep_qf {d : ℕ} (hd : 0 < d) (p : ℝ) (hp1 : p < 1) : dep d (qf p) * dep d p = 1 := by
  rw [dep_mul d hd, ← dep_zero d]
  congr 1
  unfold qf
  have : (1 - p) ≠ 0 := by linarith
  field_simp
  ring

lemma inclass_dep {d : ℕ} (hd : 0 < d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : InClass true (dep d p) := by
  refine ⟨?_, fun ρ => by simpa using dep_tp d hd p ρ⟩
  show QAlgorithms.Entanglement.IsCompletelyPositive _
  apply cp_of_choi
  rw [choi_dep]
  refine Matrix.PosSemidef.add ((Matrix.posSemidef_vecMulVec_self_star _).smul ?_)
    (Matrix.PosSemidef.one.smul ?_)
  · exact_mod_cast (sub_nonneg.mpr hp1)
  · exact_mod_cast (div_nonneg hp0 (Nat.cast_nonneg d))


lemma inclass_A {d : ℕ} (hd : 0 < d) (T : Super d) (hT : Channel T) (p : ℝ) (hp1 : p < 1)
    (hpsd : (choiMatrix (T : Mat d →ₗ[ℂ] Mat d) -
      ((p / d : ℝ) : ℂ) • Matrix.kroneckerMap (· * ·) (T 1) (1 : Mat d)).PosSemidef) :
    InClass true (T * dep d (qf p)) := by
  refine ⟨?_, fun ρ => ?_⟩
  · show QAlgorithms.Entanglement.IsCompletelyPositive _
    apply cp_of_choi
    rw [choi_A]
    have e : ((1 - qf p : ℝ) : ℂ) • choiMatrix (T : Mat d →ₗ[ℂ] Mat d) +
        ((qf p / d : ℝ) : ℂ) • Matrix.kroneckerMap (· * ·) (T 1) (1 : Mat d) =
        ((1 / (1 - p) : ℝ) : ℂ) • (choiMatrix (T : Mat d →ₗ[ℂ] Mat d) -
          ((p / d : ℝ) : ℂ) • Matrix.kroneckerMap (· * ·) (T 1) (1 : Mat d)) := by
      have h1 : (1 - p) ≠ 0 := by linarith
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, qf]
      push_cast
      have h1' : (1 - (p : ℂ)) ≠ 0 := by exact_mod_cast h1
      field_simp
      ring
    rw [e]
    exact hpsd.smul (by exact_mod_cast (le_of_lt (one_div_pos.mpr (by linarith : (0 : ℝ) < 1 - p))))
  · have h2 := hT.2 (dep d (qf p) ρ)
    simp only [ContinuousLinearMap.coe_coe] at h2 ⊢
    rw [ContinuousLinearMap.mul_apply, h2, dep_tp d hd]

lemma purity_eq {d : ℕ} (hd : 0 < d) (T : Super d) (p : ℝ) (hp1 : p < 1)
    (hU : IsUnitaryConjugation (T * dep d (qf p))) (e : Fin d) :
    ((T (Matrix.single e e 1)) * (T (Matrix.single e e 1))).trace =
      ((1 - (1 - 1 / (d : ℝ)) * (p * (2 - p)) : ℝ) : ℂ) := by
  obtain ⟨U, hU⟩ := hU
  rw [two_eq] at hU
  have hUU : (U : Mat d)ᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hT : T = adj (U : Mat d) * dep d p := by
    rw [← hU, mul_assoc, dep_qf hd p hp1, mul_one]
  rw [hT, ContinuousLinearMap.mul_apply, purity_adj _ hUU, purity_dep hd]

end G55T11

open G55T11 G55T12 G55C13 in
/-- Theorem 11, PDF p.12: a nontrivial CPTP factorization at full Choi rank.
Source correction: d>=2; the d=1 channel is unitary and indivisible. -/
theorem solution {d : ℕ} (hd : 2 ≤ d) (T : Super d)
    (hT : Channel T) (hrank : krausRank T = d ^ 2) : Divisible true T := by
  have hd0 : 0 < d := by omega
  have hJ : (QAlgorithms.Papers.Independent.Information100.P50.choiMatrix (T : Mat d →ₗ[ℂ] Mat d)).PosSemidef :=
    choi_of_cp _ hT.1
  have hJdet : (QAlgorithms.Papers.Independent.Information100.P50.choiMatrix
      (T : Mat d →ₗ[ℂ] Mat d)).det ≠ 0 := by
    apply det_of_rank
    unfold krausRank jamiolkowskiState at hrank
    rw [rank_smul _ (inv_ne_zero (by exact_mod_cast hd0.ne'))] at hrank
    rw [hrank, Fintype.card_prod, Fintype.card_fin, sq]
  have hK : (Matrix.kroneckerMap (· * ·) (T 1) (1 : Mat d)).PosSemidef :=
    (pos_of_cone hT.1 1 Matrix.PosSemidef.one).kronecker Matrix.PosSemidef.one
  obtain ⟨ε, hε, hmargin⟩ := pd_margin _ _ hJ hJdet hK
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  set p1 : ℝ := min (ε * d) (1 / 2) with hp1def
  have hp1pos : 0 < p1 := lt_min (mul_pos hε hdR) (by norm_num)
  have hp1lt : p1 ≤ 1 / 2 := min_le_right _ _
  have hp1e : p1 / d ≤ ε := by
    rw [div_le_iff₀ hdR]; exact min_le_left _ _
  have good : ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → p / d ≤ ε →
      ¬ IsUnitaryConjugation (T * dep d (qf p)) → Divisible true T := by
    intro p hp0 hp1 hpe hnu
    refine ⟨hT, T * dep d (qf p), dep d p, inclass_A hd0 T hT p (by linarith)
      (hmargin _ (div_nonneg hp0.le hdR.le) hpe), inclass_dep hd0 p hp0.le (by linarith), ?_, hnu,
      not_unit_dep hd p hp0 (by linarith)⟩
    rw [mul_assoc, dep_qf hd0 p (by linarith), mul_one]
  by_cases hU1 : IsUnitaryConjugation (T * dep d (qf p1))
  · apply good (p1 / 2) (by linarith) (by linarith)
      (le_trans (div_le_div_of_nonneg_right (by linarith) hdR.le) hp1e)
    intro hU2
    have e1 := purity_eq hd0 T p1 (by linarith) hU1 ⟨0, hd0⟩
    have e2 := purity_eq hd0 T (p1 / 2) (by linarith) hU2 ⟨0, hd0⟩
    rw [e1] at e2
    have e3 : (1 - (1 - 1 / (d : ℝ)) * (p1 * (2 - p1))) =
        1 - (1 - 1 / (d : ℝ)) * (p1 / 2 * (2 - p1 / 2)) := by exact_mod_cast e2
    have hs : 0 < 1 - 1 / (d : ℝ) := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    have e4 : p1 * (2 - p1) = p1 / 2 * (2 - p1 / 2) := by
      have := mul_left_cancel₀ hs.ne' (by linarith : (1 - 1 / (d : ℝ)) * (p1 * (2 - p1)) =
        (1 - 1 / (d : ℝ)) * (p1 / 2 * (2 - p1 / 2)))
      exact this
    nlinarith
  · exact good p1 hp1pos hp1lt hp1e hU1
