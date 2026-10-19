-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.yLeafCount_pos_of_eval_eq_matchingMarkedPermanent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/38219266-234f-476c-836f-16197ed8abbd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_pderiv_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
variable {ι : Type u} {κ : Type v} {R : Type w}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution
    {n : ℕ} {Y : Type u} [Nonempty Y]
    (d : Y ↪ Fin n × Fin n)
    (f : RationalFormula (Y ⊕ matchingOutside d) ℂ)
    (hf : eval f =
      algebraMap (MvPolynomial (Y ⊕ matchingOutside d) ℂ)
        (FractionRing (MvPolynomial (Y ⊕ matchingOutside d) ℂ))
        (matchingMarkedPermanent d)) :
    0 < yLeafCount f := by
  classical
  apply Nat.pos_of_ne_zero
  intro hzero
  obtain ⟨c, hc⟩ :=
    exists_splitEval_eq_coefficient_of_yLeafCount_eq_zero f hzero
  have hsplit :
      splitPolynomialHom (Y := Y) (Z := matchingOutside d) (F := ℂ)
          (matchingMarkedPermanent d) =
        splitCoefficientHom (Y := Y) (Z := matchingOutside d) (F := ℂ) c := by
    rw [splitEval, hf, splitFractionHom_algebraMap] at hc
    exact hc
  let E := rationalCoefficientField (matchingOutside d) ℂ
  have hpoly :
      MvPolynomial.map
          (algebraMap (MvPolynomial (matchingOutside d) ℂ) E)
          (MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)
            (matchingMarkedPermanent d)) =
        MvPolynomial.C c := by
    apply IsFractionRing.injective
      (MvPolynomial Y E) (rationalSplitField Y (matchingOutside d) ℂ)
    simpa [splitPolynomialHom, splitCoefficientHom, E] using hsplit
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hderiv := congrArg (MvPolynomial.pderiv y) hpoly
  have hmarked :
      MvPolynomial.pderiv (.inl y) (matchingMarkedPermanent d) = 0 := by
    apply (MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)).injective
    apply MvPolynomial.map_injective
      (algebraMap (MvPolynomial (matchingOutside d) ℂ) E)
      (IsFractionRing.injective (MvPolynomial (matchingOutside d) ℂ) E)
    simpa [MvPolynomial.pderiv_map, MvPolynomial.pderiv_sumAlgEquiv]
      using hderiv
  exact matchingMarkedPermanent_pderiv_ne_zero d y hmarked
end PermanentFormulaLowerBound.RationalFormula
