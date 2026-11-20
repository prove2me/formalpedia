-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:59:35.952593+00:00
-- url     : https://prove2.me/submissions/6b92b8a8-af4f-4550-b4cc-f3f99ab80e31

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiber_jointClosure_eq_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJointTensorMap_surjective_of_jointClosure
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective
      (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  exact lpsOriginalJointTensorMap_surjective_of_jointClosure (R := ZMod p) (A := K) (B := K) (C := F) _ _
    (lpsOriginalRelativeGaussNormalizationFiber_jointClosure_eq_top N p hNp h4N hN hpN q)
end QEC.Coding.TannerLiftedProduct
