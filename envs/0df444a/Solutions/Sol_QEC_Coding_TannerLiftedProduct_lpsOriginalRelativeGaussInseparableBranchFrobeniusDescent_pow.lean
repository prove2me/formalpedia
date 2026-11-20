-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:00:20.438023+00:00
-- url     : https://prove2.me/submissions/19400b5e-dc8f-4e64-b64d-68026732687a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (x : LPSOriginalRelativeGaussInseparableBranch N hN p q) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
      (lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q x) = x^p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
    lpsOriginalGaussMaximalResidue_charP N hN p q
  let : Fact (Irreducible ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) :=
      ⟨lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible N hN p hpN q⟩
  exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_pow p _ x
end QEC.Coding.TannerLiftedProduct
