-- Prove2me | solution 1 for WeilConjectures.exists_unit_cob_of_toMatrix_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T04:51:08.726272+00:00
-- url     : https://prove2.me/submissions/438d2006-7677-4cdb-8a30-5cb040966049

import Mathlib

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hdiag : ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d M)) :
    ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * M * Q = Matrix.diagonal (d M) := by
  intro M
  obtain ⟨bSrc, bTgt, h⟩ := hdiag M
  set E := Pi.basisFun (Polynomial K) ι
  -- change of basis: `M` is the standard-basis matrix of `toLin' M`
  have hM : E.toMatrix bTgt * Matrix.diagonal (d M) * bSrc.toMatrix E = M := by
    rw [← h, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  refine ⟨bTgt.toMatrix E, E.toMatrix bSrc, ?_, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip E bTgt)
  · exact Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip bSrc E)
  · conv_lhs => rw [← hM]
    simp only [Matrix.mul_assoc, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]
