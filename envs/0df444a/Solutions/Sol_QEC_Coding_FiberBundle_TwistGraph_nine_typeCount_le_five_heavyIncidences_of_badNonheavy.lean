-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.nine_typeCount_le_five_heavyIncidences_of_badNonheavy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:10:15.387965+00:00
-- url     : https://prove2.me/submissions/800ea91e-cf77-4073-bbff-7710ab01ef1b

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborIncidenceCount_univ
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_neighborIncidenceCount_union
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_disjoint_nonheavyLayerSet_heavyLayerSet
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_nonheavyLayerSet_union_heavyLayerSet
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell)
    (hu : u ∈ badNonheavyLayerSet Delta twistSample w) :
    9 * typeCount ≤
      5 *
        neighborIncidenceCount twistSample
          (heavyLayerSet Delta w) u := by
  have hu' := (mem_badNonheavyLayerSet_iff
    Delta twistSample w u).mp hu
  have hnotUsable :
      ¬ typeCount ≤
        5 *
          neighborIncidenceCount twistSample
            (nonheavyLayerSet Delta w) u := by
    intro h
    exact hu'.2 ((mem_usableNonheavyLayerSet_iff
      Delta twistSample w u).mpr ⟨hu'.1, h⟩)
  have hpartition :=
    neighborIncidenceCount_union twistSample
      (nonheavyLayerSet Delta w) (heavyLayerSet Delta w)
      (disjoint_nonheavyLayerSet_heavyLayerSet Delta w) u
  rw [nonheavyLayerSet_union_heavyLayerSet,
    neighborIncidenceCount_univ] at hpartition
  omega
end QEC.Coding.FiberBundle.TwistGraph
