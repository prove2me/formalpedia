-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.weightReducedBoundary_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:24:59.146238+00:00
-- url     : https://prove2.me/submissions/298cd8c5-2878-4e7f-a075-0c61c87f82d6

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_originalBoundary_incidenceRelation_eq
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_boundary1_surjective_of_homotopyEquiv
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hasNoIsolatedVertices_of_isFullyGood


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Function.Surjective
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (incidenceRelation sample)) := by
  let hNoIsolated :=
    hasNoIsolatedVertices_of_isFullyGood sample hDelta hGood
  let e :=
    ClassicalWeightReduction.classicalWeightReductionHomotopyEquiv
      (F₀ := ZMod 2) (incidenceRelation sample) hNoIsolated
  apply boundary1_surjective_of_homotopyEquiv e
  change Function.Surjective
    (ClassicalWeightReduction.originalBoundary (F := ZMod 2)
      (incidenceRelation sample))
  rw [originalBoundary_incidenceRelation_eq]
  exact hGood.1.2.1
end QEC.Coding.FiberBundle.RandomBase
