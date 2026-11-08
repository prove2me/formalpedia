-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.card_bitNeighbor_incidenceRelation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:05:10.071644+00:00
-- url     : https://prove2.me/submissions/07c39361-30fb-4fc8-ac37-c2bcddd6d5bd

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} (sample : Sample r) (b : Fin (4 * r)) :
    Fintype.card
        (ClassicalWeightReduction.BitNeighbor
          (incidenceRelation sample) b) =
      variableDegree sample b := by
  exact Fintype.card_subtype (fun a : Fin (3 * r) => sample (a, b) = true)
end QEC.Coding.FiberBundle.RandomBase
