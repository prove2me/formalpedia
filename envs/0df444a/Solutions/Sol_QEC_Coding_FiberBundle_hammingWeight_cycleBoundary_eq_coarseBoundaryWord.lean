-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_cycleBoundary_eq_coarseBoundaryWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:09:34.412025+00:00
-- url     : https://prove2.me/submissions/309b8ae9-be6d-494d-8358-df6a76dbc55e

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingSupport_cycleBoundary_eq_image_coarseBoundaryWord
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layerEmbedding_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    HammingWeight (cycleFiberChainBoundary (ell * ell) v) =
      HammingWeight (coarseBoundaryWord ell v) := by
  rw [HammingWeight, HammingWeight,
    hammingSupport_cycleBoundary_eq_image_coarseBoundaryWord
      ell v hBoundarySupport,
    Finset.card_image_of_injective _
      (TwistGraph.layerEmbedding_injective ell)]
end QEC.Coding.FiberBundle
