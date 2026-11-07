-- Prove2me | solution 1 for QEC.Coding.FiberBundle.coarseBoundaryWord_eq_cycleFiberChainBoundary_coarseFiberWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:06:56.028634+00:00
-- url     : https://prove2.me/submissions/5793f5b7-ce85-4747-823c-abace896c332

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberChainBoundary_apply
import Theorems.Thm_QEC_Coding_FiberBundle_cycleWord_block_constant_of_boundary_supported_at_zero_residue
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockPosition_previous


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    coarseBoundaryWord ell v =
      cycleFiberChainBoundary ell (coarseFiberWord ell v) := by
  have hTwo : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  funext u
  rw [coarseBoundaryWord,
    cycleFiberChainBoundary_apply (ell * ell) (by nlinarith),
    cycleFiberChainBoundary_apply ell hTwo]
  change
    v (TwistGraph.layerEmbedding ell u) +
        v (TwistGraph.layerEmbedding ell u - 1) =
      v (TwistGraph.layerEmbedding ell u) +
        v (TwistGraph.layerEmbedding ell (u - 1))
  congr 1
  have hBlock :=
    cycleWord_block_constant_of_boundary_supported_at_zero_residue
      ell v hBoundarySupport (u - 1)
        ⟨ell - 1, Nat.sub_lt (NeZero.pos ell) Nat.zero_lt_one⟩
  rw [TwistGraph.blockPosition_previous] at hBlock
  exact hBlock
end QEC.Coding.FiberBundle
