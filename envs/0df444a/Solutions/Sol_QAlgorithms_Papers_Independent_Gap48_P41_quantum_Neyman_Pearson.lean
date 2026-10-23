-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P41.quantum_Neyman_Pearson
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:50:41.2223+00:00
-- url     : https://prove2.me/submissions/8c76cc3a-94b3-453a-88e6-1c9addf2f111

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41

noncomputable section

open scoped Matrix ComplexOrder BigOperators MatrixOrder

namespace X6G41

open QAlgorithms.Papers.Independent.Information100.P07

variable {J : Type} [Fintype J] [DecidableEq J]

lemma tel_mul (A B : Matrix J J ℂ) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, map_mul]
  rfl

lemma tel_proj (S : Submodule ℂ (EuclideanSpace ℂ J)) :
    Matrix.toEuclideanLin (projection S) = S.starProjection.toLinearMap := by
  simp [projection]

lemma proj_herm (S : Submodule ℂ (EuclideanSpace ℂ J)) : (projection S).IsHermitian := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, tel_proj]
  exact S.starProjection_isSymmetric

lemma proj_idem (S : Submodule ℂ (EuclideanSpace ℂ J)) :
    projection S * projection S = projection S := by
  apply Matrix.toEuclideanLin.injective
  rw [tel_mul, tel_proj]
  ext1 x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Submodule.starProjection_eq_self_iff]
  exact Submodule.starProjection_apply_mem S x

lemma psd_of_proj {P : Matrix J J ℂ} (hH : P.IsHermitian) (hI : P * P = P) : P.PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hH.eq, hI] at this

lemma proj_mul_N (N : Matrix J J ℂ) :
    projection (operatorRange N) * N = N := by
  apply Matrix.toEuclideanLin.injective
  rw [tel_mul, tel_proj]
  ext1 x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [Submodule.starProjection_eq_self_iff]
  exact LinearMap.mem_range_self _ x

lemma Bp_mul_proj (N Bp : Matrix J J ℂ) (h : Bp * N = 0) :
    Bp * projection (operatorRange N) = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [tel_mul, tel_proj, map_zero]
  ext1 x
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply]
  obtain ⟨y, hy⟩ : (operatorRange N).starProjection x ∈ LinearMap.range (Matrix.toEuclideanLin N) :=
    Submodule.starProjection_apply_mem _ x
  rw [← hy, ← LinearMap.comp_apply, ← tel_mul, h, map_zero, LinearMap.zero_apply]

lemma tr_nonneg {A B : Matrix J J ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  have hA0 : (0 : Matrix J J ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hs : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have e : A = CFC.sqrt A * CFC.sqrt A := (CFC.sqrt_mul_sqrt_self A hA0).symm
  rw [e, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have := (hB.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg
  rw [hs.1.eq] at this
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp this).1

/-- Neyman-Pearson for a Hermitian `B`. -/
theorem np (B : Matrix J J ℂ) (hB : B.IsHermitian) (A : Matrix J J ℂ)
    (hA : A.PosSemidef) (hA1 : (1 - A).PosSemidef) :
    (1 - positiveProjection (-B)).PosSemidef ∧ (1 - (1 - positiveProjection (-B))).PosSemidef ∧
    (B * A).trace.re ≤ (B * (1 - positiveProjection (-B))).trace.re := by
  set N := cfc (fun t : ℝ => max (-t) 0) B with hNdef
  set Bp := cfc (fun t : ℝ => max t 0) B with hBpdef
  have hsa : IsSelfAdjoint B := hB.isSelfAdjoint
  have hN : positivePart (-B) = N := by
    rw [positivePart, hNdef, ← cfc_comp_neg (fun t : ℝ => max t 0) B]
  have hsplit : B = Bp - N := by
    rw [hBpdef, hNdef, ← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) B]
    conv_lhs => rw [← cfc_id ℝ B]
    apply cfc_congr
    intro t _
    simp only [id]
    rcases le_total t 0 with h | h <;> simp [h]
  have hprod : Bp * N = 0 := by
    rw [hBpdef, hNdef, ← cfc_mul (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) B]
    rw [← cfc_zero ℝ B]
    apply cfc_congr
    intro t _
    rcases le_total t 0 with h | h <;> simp [h]
  have hBpP : Bp.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun t _ => le_max_right _ _)
  have hNP : N.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun t _ => le_max_right _ _)
  have hPP : positiveProjection (-B) = projection (operatorRange N) := by
    rw [positiveProjection, support, hN]
  rw [hPP]
  set P := projection (operatorRange N)
  have hPH := proj_herm (operatorRange N)
  have hPI := proj_idem (operatorRange N)
  have hQH : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hPH
  have hQI : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPI]; simp [P]
  refine ⟨psd_of_proj hQH hQI, ?_, ?_⟩
  · rw [sub_sub_cancel]; exact psd_of_proj hPH hPI
  · have hPN : P * N = N := proj_mul_N N
    have hNP' : N * P = N := by
      have := congrArg Matrix.conjTranspose hPN
      rwa [Matrix.conjTranspose_mul, hPH.eq, hNP.1.eq] at this
    have hBpP' : Bp * P = 0 := Bp_mul_proj N Bp hprod
    have e1 : B * (1 - P) = Bp := by
      rw [hsplit, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hBpP', hNP']; simp
    rw [e1, hsplit, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    have h1 := tr_nonneg hNP hA
    have h2 := tr_nonneg hBpP hA1
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_one] at h2
    linarith

end X6G41

namespace QAlgorithms.Papers.Independent.Gap48.P41

open scoped Matrix ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (tr SupportLE relativeEntropy scalarPower classicalD typeI accept TestSequence
    scaled logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Claimed50.P15 (legendre)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

lemma x6_copies_herm {m : ℕ} (X : Mat I) (hX : X.IsHermitian) : (copies m X).IsHermitian := by
  ext x y
  simp only [copies, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact congrFun (congrFun hX (x i)) (y i)

end QAlgorithms.Papers.Independent.Gap48.P41

open QAlgorithms.Papers.Independent.Gap48.P41
open Filter QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr SupportLE)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

theorem solution [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (n : ℕ) (hn : 0 < n) (lambda : ℝ)
    (A : Mat (Fin n → I)) (hA : IsEffect A) :
    IsEffect (nonnegativeProjection (blockDifference rho sigma n lambda)) ∧
    tr (blockDifference rho sigma n lambda * A) ≤
      tr (blockDifference rho sigma n lambda *
        nonnegativeProjection (blockDifference rho sigma n lambda)) := by
  have hB : (blockDifference rho sigma n lambda).IsHermitian := by
    unfold blockDifference
    refine (x6_copies_herm rho hrho.1.1).sub ?_
    refine IsSelfAdjoint.smul ?_ (x6_copies_herm sigma hsigma.1.1)
    exact Complex.conj_ofReal _
  obtain ⟨h1, h2, h3⟩ := X6G41.np _ hB A hA.1 hA.2
  exact ⟨⟨h1, h2⟩, h3⟩
