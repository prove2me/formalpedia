-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalFrickeLevelPullback_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:00:15.195855+00:00
-- url     : https://prove2.me/submissions/b5b9f202-c3f3-4db2-85e8-bebeb971589a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntermediateFieldInclusion_finrank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM) :=
      (lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM).toAlgebra
    letI : Module (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGeneratedFunctionFieldQ M hM) := Algebra.toModule
    Module.finrank (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM) =
      (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank (lpsOriginalGeneratedFunctionFieldQ M hM) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f := lpsOriginalRationalFrickeLevelPullback N M hNM h4N hN hM
  let g := (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom
  let eN := lpsOriginalRationalFrickeEquiv N hN
  let eM := lpsOriginalRationalFrickeEquiv M hM
  have he : g.comp eN.toRingHom = eM.toRingHom.comp f := by
    apply RingHom.ext
    intro x
    change g (lpsOriginalRationalFrickePullback N hN x) =
      lpsOriginalRationalFrickePullback M hM
        (lpsOriginalRationalFrickePullback M hM (g (lpsOriginalRationalFrickePullback N hN x)))
    rw [lpsOriginalRationalFrickePullback_involutive]
  have hr := @Algebra.finrank_eq_of_equiv_equiv
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM)
    inferInstance inferInstance f.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionFieldQ M hM)
    inferInstance inferInstance g.toAlgebra eN eM he
  exact hr.trans (lpsOriginalIntermediateFieldInclusion_finrank _ _
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM h4N hN hM))
end QEC.Coding.TannerLiftedProduct
