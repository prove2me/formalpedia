-- Prove2me | solution 1 for complex_psd_det_le_prod_diag
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:08:55.314574+00:00
-- url     : https://prove2.me/submissions/95dc365d-f7a6-4495-9543-6c5ebf2137de

import Mathlib
open Matrix InnerProductSpace
open scoped MatrixOrder ComplexConjugate ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

private lemma normDet_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    f.normDet ≤ ∏ i, ‖f (EuclideanSpace.basisFun ι ℂ i)‖ := by
  let v := fun i => f (EuclideanSpace.basisFun ι ℂ i)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι := by simp
  let b := gramSchmidtOrthonormalBasis hdim v
  have hb := gramSchmidtOrthonormalBasis_det hdim v
  rw [f.normDet_eq_norm_det_toMatrix (EuclideanSpace.basisFun ι ℂ) b]
  have he : LinearMap.toMatrix (EuclideanSpace.basisFun ι ℂ).toBasis b.toBasis f =
      b.toBasis.toMatrix v := by
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply, v]
  rw [he, ← Module.Basis.det_apply]
  change ‖b.toBasis.det v‖ ≤ ∏ i, ‖v i‖
  rw [hb, norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i _
  calc
    ‖inner ℂ (b i) (v i)‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]

theorem solution {idx : Type*} [Fintype idx] [DecidableEq idx]
    (B : Matrix idx idx ℂ) (hB : B.PosSemidef) :
    B.det.re ≤ ∏ i, (B i i).re := by
  letI : LinearOrder idx := LinearOrder.lift' (Fintype.equivFin idx) (Fintype.equivFin idx).injective
  letI : LocallyFiniteOrderBot idx := LocallyFiniteOrderBot.ofIic' idx
    (fun i => Finset.univ.filter (fun j => j ≤ i)) (by intro i j; simp)
  let R := CFC.sqrt B
  have hR : Rᴴ = R := (CFC.sqrt_nonneg B).star_eq
  have hRR : Rᴴ * R = B := by
    rw [hR]
    exact CFC.sqrt_mul_sqrt_self B (by simpa only [Matrix.nonneg_iff_posSemidef] using hB)
  let f := Matrix.toEuclideanLin R
  let b := EuclideanSpace.basisFun idx ℂ
  let v := fun i => f (b i)
  have hv (i : idx) : v i = WithLp.toLp 2 (fun j => R j i) := by
    simp [v, f, b, EuclideanSpace.basisFun_apply, Matrix.toEuclideanLin_apply,
      EuclideanSpace.single, Matrix.mulVec_single, Matrix.col, Matrix.transpose]
    rfl
  have hgram : Matrix.gram ℂ v = B := by
    rw [Matrix.gram_eq_conjTranspose_mul b]
    have hc : (Matrix.of (fun i j => b.repr (v j) i)) = R := by
      ext i j
      simp [b, hv]
    rw [hc, hRR]
  have hdet : B.det.re = f.normDet ^ 2 := by
    have hd := f.normDet_sq_eq_det_gram b
    rw [hgram] at hd
    exact (congrArg Complex.re hd).symm
  have hdiag (i : idx) : (B i i).re = ‖v i‖ ^ 2 := by
    rw [← hgram]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v i)).symm
  rw [hdet]
  simp_rw [hdiag]
  rw [Finset.prod_pow]
  apply pow_le_pow_left₀ f.normDet_nonneg
  exact normDet_le_prod f
