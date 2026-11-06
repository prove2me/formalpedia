-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.layerEmbedding_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:42:37.007745+00:00
-- url     : https://prove2.me/submissions/0db92dc4-3817-4f66-8fa1-da2e29f9893d

import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) :
    layerEmbedding ell (step sample τ) =
      multipleRotation ell
        ⟨(RandomTwist.typeTwist sample τ).val + 1, by
          have h := (RandomTwist.typeTwist sample τ).isLt
          omega⟩ := by
  rw [step, layerEmbedding_natCast]
  rfl
end QEC.Coding.FiberBundle.TwistGraph
