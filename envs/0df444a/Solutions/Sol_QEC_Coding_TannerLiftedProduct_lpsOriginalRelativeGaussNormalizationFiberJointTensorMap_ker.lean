-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:57:16.978312+00:00
-- url     : https://prove2.me/submissions/b1b15b5a-734b-458e-b1ae-9975950e1302

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRingHom_prod_ker
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_generatedDiagram
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
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : CharP F p := charP_of_injective_ringHom
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    letI : Module (ZMod p) K := Algebra.toModule
    letI : Module (ZMod p) F := Algebra.toModule
    RingHom.ker (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q).toRingHom =
      RingHom.ker (lpsOriginalFrobeniusFirstTensorGraphMap p K).toRingHom ⊓
        RingHom.ker (lpsOriginalFrobeniusSecondTensorGraphMap p K).toRingHom := by
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
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  rw [← RingHom.ker_comp_of_injective (f := e.toRingHom)
    (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q).toRingHom e.injective,
    lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_generatedDiagram]
  exact lpsOriginalRingHom_prod_ker _ _
end QEC.Coding.TannerLiftedProduct
