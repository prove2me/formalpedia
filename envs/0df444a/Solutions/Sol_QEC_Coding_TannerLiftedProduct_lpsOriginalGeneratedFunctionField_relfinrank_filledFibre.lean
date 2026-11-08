-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_relfinrank_filledFibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:10:50.126188+00:00
-- url     : https://prove2.me/submissions/18ae0288-3e1f-4697-8c31-25d4cd1ba35f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_relfinrank_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInteriorForgetLevel_fibre_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField M hposM) =
      Nat.card {x : LPSOriginalFilledCurve M |
        lpsOriginalFilledForgetLevel N M hNM x = Sum.inl y} := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [lpsOriginalGeneratedFunctionField_relfinrank_eq N M hNM hN hposN hposM]
  exact (lpsOriginalInteriorForgetLevel_fibre_card N M hNM hN y).symm.trans
    (Nat.card_congr (lpsOriginalFilledInteriorFibreEquiv N M hNM y))
end QEC.Coding.TannerLiftedProduct
