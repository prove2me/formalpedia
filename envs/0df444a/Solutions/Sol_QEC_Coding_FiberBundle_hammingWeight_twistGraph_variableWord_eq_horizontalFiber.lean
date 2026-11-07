-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_twistGraph_variableWord_eq_horizontalFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:09:32.394407+00:00
-- url     : https://prove2.me/submissions/9d81a26b-bb0b-4424-b585-947af76a1814

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingSupport_horizontalFiber_eq_image_twistGraph_variableWord
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layerEmbedding_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z)
    (b : Fin (4 * r)) :
    HammingWeight
        (TwistGraph.variableWord
          (twistGraphWordOfHorizontalComponent z) b) =
      HammingWeight (horizontalFiber z b) := by
  rw [HammingWeight, HammingWeight,
    hammingSupport_horizontalFiber_eq_image_twistGraph_variableWord
      z hNormalized b,
    Finset.card_image_of_injective _
      (TwistGraph.layerEmbedding_injective ell)]
end QEC.Coding.FiberBundle
