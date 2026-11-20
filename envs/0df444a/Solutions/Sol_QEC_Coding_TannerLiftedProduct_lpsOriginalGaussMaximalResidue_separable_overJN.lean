-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_separable_overJN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:07:06.425533+00:00
-- url     : https://prove2.me/submissions/7304b3a8-9acd-43cd-81d6-9e3bf3b62401

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJ_separable_overJN
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_adjoinJ_overJN_eq_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
    Algebra.IsSeparable (FractionRing (Polynomial (ZMod p)))
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
  let : Algebra.IsSeparable (FractionRing (Polynomial (ZMod p)))
      (IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
        {lpsOriginalGaussMaximalResidueJ N hN p q}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr
      (lpsOriginalGaussMaximalResidueJ_separable_overJN N hN p hpN q)
  let e := (IntermediateField.equivOfEq
    (lpsOriginalGaussMaximalResidue_adjoinJ_overJN_eq_top N hN p hpN q)).trans
    IntermediateField.topEquiv
  exact Algebra.IsSeparable.of_algHom
    (FractionRing (Polynomial (ZMod p))) _ e.symm.toAlgHom
end QEC.Coding.TannerLiftedProduct
