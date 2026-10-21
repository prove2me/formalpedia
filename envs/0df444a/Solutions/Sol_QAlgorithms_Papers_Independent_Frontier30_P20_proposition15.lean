-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P20.proposition15
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:57:23.038156+00:00
-- url     : https://prove2.me/submissions/c0ce0b67-3ace-4232-aa78-9d3b779cbbc8

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


namespace G55H
open scoped MatrixOrder

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

end G55H

namespace G55P15
open G55T12 G55H QAlgorithms.Papers.Independent.Dependency50.P28
open QAlgorithms.Papers.Independent.Dependency50.P12 (superOfAction)

lemma coef_apply {d : ℕ} (T : Super d) (p q : Fin d × Fin d) :
    superOfAction (⇑T) p q = T (Matrix.single q.1 q.2 1) p.1 p.2 := rfl

lemma coef_mul {d : ℕ} (A B : Super d) :
    superOfAction ⇑(A * B) = superOfAction ⇑A * superOfAction ⇑B := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [coef_apply, ContinuousLinearMap.mul_apply]
  rw [lin_expand A (B _)]
  simp [Matrix.sum_apply, Fintype.sum_prod_type, mul_comm]

lemma coef_one {d : ℕ} : superOfAction ⇑(1 : Super d) = 1 := by
  ext p q
  simp only [coef_apply, ContinuousLinearMap.one_apply, Matrix.single_apply, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : q.1 = p.1 <;> by_cases h2 : q.2 = p.2 <;> simp [h1, h2] <;> intro h <;> simp_all [eq_comm]

lemma coef_sub {d : ℕ} (A B : Super d) :
    superOfAction ⇑(A - B) = superOfAction ⇑A - superOfAction ⇑B := by
  ext p q; rfl

def coefL (d : ℕ) : Super d →ₗ[ℂ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ where
  toFun T := superOfAction ⇑T
  map_add' A B := by ext p q; rfl
  map_smul' c A := by ext p q; rfl

lemma det_real {d : ℕ} (A : Super d) (hA : Positive A.toLinearMap) : (complexDet A).im = 0 := by
  set C := superOfAction ⇑A with hCdef
  have hC : C.map (starRingEnd ℂ) = C.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext p q
    simp only [Matrix.map_apply, Matrix.submatrix_apply, hCdef, coef_apply]
    have := star_pres A.toLinearMap hA (Matrix.single q.1 q.2 1)
    rw [Matrix.conjTranspose_single, star_one] at this
    simp only [ContinuousLinearMap.coe_coe] at this
    simp [this, Matrix.conjTranspose_apply]
  have h := congrArg Matrix.det hC
  rw [Matrix.det_submatrix_equiv_self,
    show (C.map (starRingEnd ℂ)).det = starRingEnd ℂ C.det from (RingHom.map_det _ _).symm] at h
  exact Complex.conj_eq_iff_im.mp h


lemma near_one (d : ℕ) : ∃ δ > 0, ∀ C : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
    ‖Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ) (C - 1)‖ < δ → 0 < (C.det).re := by
  set e := Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ)
  have hsymm : Continuous (fun Y => e.symm Y) :=
    LinearMap.continuous_of_finiteDimensional e.symm.toAlgEquiv.toLinearEquiv.toLinearMap
  have hg : Continuous (fun Y => (e.symm Y).det) := hsymm.matrix_det
  obtain ⟨δ, hδ, h⟩ := (Metric.continuousAt_iff.mp (hg.continuousAt (x := e 1))) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun C hC => ?_⟩
  have h1 := h (x := e C) (by rw [dist_eq_norm, ← map_sub]; exact hC)
  simp only [StarAlgEquiv.symm_apply_apply, Matrix.det_one, dist_eq_norm] at h1
  have h2 := (Complex.abs_re_le_norm (C.det - 1)).trans_lt h1
  rw [Complex.sub_re, Complex.one_re] at h2
  have := (abs_lt.mp h2).1
  linarith

lemma fine_sub {d : ℕ} (T : Super d) (hT : T ∈ fineProducts d true false) :
    (complexDet T).im = 0 ∧ 0 < (complexDet T).re := by
  obtain ⟨δ, hδ, hnear⟩ := near_one d
  obtain ⟨_, h⟩ := hT
  obtain ⟨factors, hf, hprod⟩ := h (δ / 2) (by positivity)
  rw [← hprod]
  clear hprod
  induction factors with
  | nil =>
    rw [List.prod_nil]; unfold complexDet; rw [coef_one]; simp
  | cons A rest ih =>
    have hA := hf A (by simp)
    have ih' := ih (fun B hB => hf B (by simp [hB]))
    have hAi : (complexDet A).im = 0 := det_real A (pos_of_cone hA.1.1)
    have hAr : 0 < (complexDet A).re := by
      apply hnear
      have := hA.2.1
      unfold hsOperatorNorm at this
      rw [coef_sub, coef_one] at this
      linarith
    have hmul : complexDet (A * rest.prod) = complexDet A * complexDet rest.prod := by
      unfold complexDet; rw [coef_mul, Matrix.det_mul]
    rw [List.prod_cons, hmul, Complex.mul_im, Complex.mul_re, hAi, ih'.1]
    refine ⟨by ring, ?_⟩
    simp only [mul_zero, sub_zero]
    exact mul_pos hAr ih'.2

end G55P15

open G55P15 in
/-- Proposition 15, PDF p.13: the determinant obstruction includes singular boundary channels. -/
theorem solution {d : ℕ} (hd : 0 < d) (T : Super d)
    (hT : Channel T) (hinf : Infinitesimal true T) :
    (complexDet T).im = 0 ∧ 0 ≤ determinant T := by
  have hcont : Continuous (fun T : Super d => complexDet T) := by
    have : Continuous (fun T : Super d => coefL d T) := LinearMap.continuous_of_finiteDimensional _
    exact this.matrix_det
  have hclosed : IsClosed {T : Super d | (complexDet T).im = 0 ∧ 0 ≤ (complexDet T).re} :=
    (isClosed_eq (Complex.continuous_im.comp hcont) continuous_const).inter
      (isClosed_le continuous_const (Complex.continuous_re.comp hcont))
  have hsub : fineProducts d true false ⊆ {T : Super d | (complexDet T).im = 0 ∧ 0 ≤ (complexDet T).re} :=
    fun T hT => let h := fine_sub T hT; ⟨h.1, h.2.le⟩
  exact closure_minimal hsub hclosed hinf
