-- Prove2me | solution 1 for PermanentFormulaLowerBound.coefficientPolynomial_rename_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/832a3557-1a2c-408f-8ed7-dcec44c7ca45

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {Y : Type u} {Z : Type v} {W : Type w}
    {F : Type*} [Field F]
    (e : Z ≃ W) (f : MvPolynomial (Y ⊕ Z) F)
    (α : Y →₀ ℕ) :
    coefficientPolynomial
        (MvPolynomial.renameEquiv F
          (Equiv.sumCongr (Equiv.refl Y) e) f) α =
      MvPolynomial.renameEquiv F e (coefficientPolynomial f α) := by
  classical
  let L : MvPolynomial (Y ⊕ Z) F →ₐ[F]
      MvPolynomial Y (MvPolynomial W F) :=
    (MvPolynomial.sumAlgEquiv F Y W).toAlgHom.comp
      (MvPolynomial.renameEquiv F
        (Equiv.sumCongr (Equiv.refl Y) e)).toAlgHom
  let R : MvPolynomial (Y ⊕ Z) F →ₐ[F]
      MvPolynomial Y (MvPolynomial W F) :=
    (MvPolynomial.mapAlgHom
      (MvPolynomial.renameEquiv F e).toAlgHom).comp
      (MvPolynomial.sumAlgEquiv F Y Z).toAlgHom
  have h : L = R := by
    ext i
    cases i with
    | inl y =>
        simp [L, R, MvPolynomial.renameEquiv_apply]
    | inr z =>
        simp [L, R, MvPolynomial.renameEquiv_apply]
  change MvPolynomial.coeff α
    ((MvPolynomial.sumAlgEquiv F Y W)
      (MvPolynomial.renameEquiv F
        (Equiv.sumCongr (Equiv.refl Y) e) f)) = _
  change MvPolynomial.coeff α (L f) = _
  rw [h]
  change MvPolynomial.coeff α
    (MvPolynomial.map
      (MvPolynomial.renameEquiv F e).toRingHom
      ((MvPolynomial.sumAlgEquiv F Y Z) f)) = _
  rw [MvPolynomial.coeff_map]
  rfl
end PermanentFormulaLowerBound
