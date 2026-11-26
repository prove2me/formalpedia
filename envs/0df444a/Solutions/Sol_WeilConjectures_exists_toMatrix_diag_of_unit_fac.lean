-- Prove2me | solution 1 for WeilConjectures.exists_toMatrix_diag_of_unit_fac
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:37:28.777032+00:00
-- url     : https://prove2.me/submissions/402adc93-4d51-4465-8c85-bc392814d767

import Mathlib

/-- A64c REV-COB: unit-determinant factorization `P M Q = diag(a)` yields bases of
`K[X]^ι` in which `toLin' M` is represented by `diag(a)`.

Converse direction to `exists_unit_cob_of_toMatrix_diagonal` (503effa6).

**REUSE:** `Pi.basisFun`, `Basis.map`, `Matrix.toLin'`, `LinearMap.toMatrix`,
`Matrix.isUnit_iff_isUnit_det`. -/
theorem _root_.solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι (Polynomial K)} {a : ι → Polynomial K}
    {P Q : Matrix ι ι (Polynomial K)}
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : P * M * Q = Matrix.diagonal a) :
    ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal a := by
  have hPm : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hP
  have hQm : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 hQ
  have hQi : Invertible Q := hQm.invertible
  have hPi : Invertible P := hPm.invertible
  obtain ⟨eQ, heQ⟩ : ∃ e : (ι → Polynomial K) ≃ₗ[Polynomial K] (ι → Polynomial K), ∀ x, e x = Matrix.toLin' Q x :=
    ⟨Matrix.toLinearEquiv' Q hQi, fun x => rfl⟩
  obtain ⟨eP, heP⟩ : ∃ e : (ι → Polynomial K) ≃ₗ[Polynomial K] (ι → Polynomial K), ∀ x, e x = Matrix.toLin' P x :=
    ⟨Matrix.toLinearEquiv' P hPi, fun x => rfl⟩
  refine ⟨(Pi.basisFun (Polynomial K) ι).map eQ, (Pi.basisFun (Polynomial K) ι).map eP.symm, ?_⟩
  ext1 i j
  rw [LinearMap.toMatrix_apply]
  simp only [Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, Pi.basisFun_repr]
  rw [heQ, heP, Pi.basisFun_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  rw [h, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

