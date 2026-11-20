-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_frobenius_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:57:59.79852+00:00
-- url     : https://prove2.me/submissions/ee3447b8-f2b1-493b-acd4-36f7dca731bc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranch_finrank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : Algebra K K := (frobenius K p).toAlgebra
    letI : Module K K := Algebra.toModule
    Module.finrank K K = p := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let : Algebra K T := inferInstance
  let : Algebra K K := (frobenius K p).toAlgebra
  let : Module K K := Algebra.toModule
  have hd := lpsOriginalRelativeGaussInseparableBranch_finrank N hN p q
  have he := (lpsOriginalRelativeGaussInseparableBranchFrobeniusAlgEquiv
    N p hNp h4N hN hpN q).toLinearEquiv.finrank_eq
  exact he.symm.trans hd
end QEC.Coding.TannerLiftedProduct
