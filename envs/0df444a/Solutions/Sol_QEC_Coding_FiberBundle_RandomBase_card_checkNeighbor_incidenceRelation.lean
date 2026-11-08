-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.card_checkNeighbor_incidenceRelation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:04:31.348342+00:00
-- url     : https://prove2.me/submissions/0fb0d613-55ba-47e5-b61c-1f1b2bf2092a

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} (sample : Sample r) (a : Fin (3 * r)) :
    Fintype.card
        (ClassicalWeightReduction.CheckNeighbor
          (incidenceRelation sample) a) =
      checkDegree sample a := by
  exact Fintype.card_subtype (fun b : Fin (4 * r) => sample (a, b) = true)
end QEC.Coding.FiberBundle.RandomBase
