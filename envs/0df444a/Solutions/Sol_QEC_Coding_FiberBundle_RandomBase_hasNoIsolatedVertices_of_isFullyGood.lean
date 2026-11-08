-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.hasNoIsolatedVertices_of_isFullyGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:11:38.666202+00:00
-- url     : https://prove2.me/submissions/6399e96d-ec14-456c-9294-48ceacd15886

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hasNoIsolatedVertices_of_degreeWindows

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r Delta : Nat} (sample : Sample r)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    ClassicalWeightReduction.HasNoIsolatedVertices
      (incidenceRelation sample) :=
  hasNoIsolatedVertices_of_degreeWindows sample hDelta hGood.1.1
end QEC.Coding.FiberBundle.RandomBase
