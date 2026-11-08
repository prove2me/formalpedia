-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.finrank_weightReducedComplex_middleHomology_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:26:01.002289+00:00
-- url     : https://prove2.me/submissions/fc2a7d44-cc0d-4ae2-9394-c0049f441a86

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_finrank_originalComplex_middleHomology_eq
import Theorems.Thm_QEC_Coding_ChainComplexData_finrank_middleHomology_eq
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hasNoIsolatedVertices_of_isFullyGood
import Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_finrank_middleHomology_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Module.finrank (ZMod 2)
        (ClassicalWeightReduction.weightReducedComplex (F₀ := ZMod 2)
          (incidenceRelation sample)).middleHomology = r := by
  let hNoIsolated :=
    hasNoIsolatedVertices_of_isFullyGood sample hDelta hGood
  let e :=
    ClassicalWeightReduction.classicalWeightReductionHomotopyEquiv
      (F₀ := ZMod 2) (incidenceRelation sample) hNoIsolated
  calc
    Module.finrank (ZMod 2)
        (ClassicalWeightReduction.weightReducedComplex (F₀ := ZMod 2)
          (incidenceRelation sample)).middleHomology =
      Module.finrank (ZMod 2)
        (ClassicalWeightReduction.originalComplex (F₀ := ZMod 2)
          (incidenceRelation sample)).middleHomology :=
      e.finrank_middleHomology_eq
    _ = r := finrank_originalComplex_middleHomology_eq sample hGood
end QEC.Coding.FiberBundle.RandomBase
