-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineGenerated_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:34:57.979821+00:00
-- url     : https://prove2.me/submissions/3e0ff90c-92d0-4887-b825-883233872d3f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineToGenerated_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerAffineToGenerated N hN).toAlgebra
    IsFractionRing (lpsOriginalIntegerAffineRing N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerAffineToGenerated N hN).toAlgebra
  let := lpsOriginalIntegerAffineRing_domain N hN
  let : FaithfulSMul (lpsOriginalIntegerAffineRing N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (lpsOriginalIntegerAffineToGenerated_injective N hN)
  apply IsFractionRing.of_field
  intro x
  have hx : (x:LPSOriginalHolomorphicFractionField) ∈
      (lpsOriginalIntegerAffineFractionEmbedding N hN).fieldRange := by
    rw [lpsOriginalIntegerAffineFractionEmbedding_range N hN]
    exact x.property
  obtain ⟨z,hz⟩ := hx
  obtain ⟨a,b,_,hab⟩ := IsFractionRing.div_surjective
    (lpsOriginalIntegerAffineRing N hN) z
  refine ⟨a,b,?_⟩
  apply Subtype.val_injective
  change (x:LPSOriginalHolomorphicFractionField)=
    lpsOriginalIntegerAffineLocalizedEval N hN a /
      lpsOriginalIntegerAffineLocalizedEval N hN b
  rw [←hz,←hab,map_div₀,
    lpsOriginalIntegerAffineFractionEmbedding_algebraMap N hN a,
    lpsOriginalIntegerAffineFractionEmbedding_algebraMap N hN b]
end QEC.Coding.TannerLiftedProduct
