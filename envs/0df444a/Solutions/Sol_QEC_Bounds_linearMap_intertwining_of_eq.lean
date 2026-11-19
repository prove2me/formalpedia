-- Prove2me | solution 1 for QEC.Bounds.linearMap_intertwining_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-18T07:03:48.714707+00:00
-- url     : https://prove2.me/submissions/601414d3-1e3a-422a-905c-1968b1335d7c

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_JointCoordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_IntertwiningAlgebra

set_option autoImplicit false
open QEC
open QEC.Bounds
universe u
namespace QEC.Bounds
theorem _root_.solution
    {H K : Type u}
    [AddCommMonoid H] [Module Complex H]
    [AddCommMonoid K] [Module Complex K]
    (embedding coordinates : H →ₗ[Complex] K)
    (physical : K →ₗ[Complex] K) (logical : H →ₗ[Complex] H)
    (hembedding : embedding = coordinates)
    (hcoordinates : physical.comp coordinates = coordinates.comp logical) :
    physical.comp embedding = embedding.comp logical := by
  rw [hembedding]
  exact hcoordinates
end QEC.Bounds
