-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_separable_overJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:58:03.831002+00:00
-- url     : https://prove2.me/submissions/160b1dde-51b5-440e-9ac2-67b1144a6008

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_separable_overJ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_adjoinJN_overJ_eq_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
    Algebra.IsSeparable (FractionRing (Polynomial (ZMod p)))
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
  let : Algebra.IsSeparable (FractionRing (Polynomial (ZMod p)))
      (IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
        {lpsOriginalGaussMaximalResidueJN N hN p q}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr
      (lpsOriginalGaussMaximalResidueJN_separable_overJ N hN p hpN q)
  let e := (IntermediateField.equivOfEq
    (lpsOriginalGaussMaximalResidue_adjoinJN_overJ_eq_top N hN p q)).trans
    IntermediateField.topEquiv
  exact Algebra.IsSeparable.of_algHom
    (FractionRing (Polynomial (ZMod p))) _ e.symm.toAlgHom
end QEC.Coding.TannerLiftedProduct
