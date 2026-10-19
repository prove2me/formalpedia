-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_algebraicIndependent_of_prodCongr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/abff4687-2bbc-4d7c-ba6c-7f9c657f4b7c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_coefficientPolynomial_rename_outside
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_rename_prodCongr

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} {Y : Type u} {ι : Type v}
    (d₀ d : Y ↪ Fin n × Fin n)
    (r c : Equiv.Perm (Fin n))
    (he : ∀ y : Y, Equiv.prodCongr r c (d₀ y) = d y)
    (α : ι → Y →₀ ℕ)
    (hind : AlgebraicIndependent ℂ
      (fun i => coefficientPolynomial
        (matchingMarkedPermanent d₀) (α i))) :
    AlgebraicIndependent ℂ
      (fun i => coefficientPolynomial
        (matchingMarkedPermanent d) (α i)) := by
  let eo := matchingOutsideRelabelEquiv d₀ d
    (Equiv.prodCongr r c) he
  have hmap : AlgebraicIndependent ℂ
      (fun i => MvPolynomial.renameEquiv ℂ eo
        (coefficientPolynomial (matchingMarkedPermanent d₀) (α i))) := by
    change AlgebraicIndependent ℂ
      ((MvPolynomial.renameEquiv ℂ eo).toAlgHom ∘
        fun i => coefficientPolynomial (matchingMarkedPermanent d₀) (α i))
    exact hind.map' (MvPolynomial.renameEquiv ℂ eo).injective
  have hcoeff (i : ι) :
      coefficientPolynomial (matchingMarkedPermanent d) (α i) =
        MvPolynomial.renameEquiv ℂ eo
          (coefficientPolynomial (matchingMarkedPermanent d₀) (α i)) := by
    rw [← matchingMarkedPermanent_rename_prodCongr d₀ d r c he]
    exact coefficientPolynomial_rename_outside eo
      (matchingMarkedPermanent d₀) (α i)
  rw [show (fun i => coefficientPolynomial
      (matchingMarkedPermanent d) (α i)) =
      (fun i => MvPolynomial.renameEquiv ℂ eo
        (coefficientPolynomial (matchingMarkedPermanent d₀) (α i)))
    from funext hcoeff]
  exact hmap
end PermanentFormulaLowerBound
