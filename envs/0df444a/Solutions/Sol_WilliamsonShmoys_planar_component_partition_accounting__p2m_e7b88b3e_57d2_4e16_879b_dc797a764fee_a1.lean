-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_partition_accounting__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:51.440973+00:00
-- url     : https://prove2.me/submissions/65631a53-4089-46c9-acd2-40cbdd1cf92f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_component_partition__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
import Theorems.Thm_WilliamsonShmoys_partition_edge_accounting__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) :
    ∃ C : V → Finset V,
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (Finset.univ.biUnion C = Finset.univ) ∧
      (L.edgeSet.ncard = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard) := by
  obtain ⟨C, hdisjoint, hcover, hlocal⟩ :=
    WilliamsonShmoys.finite_graph_component_partition__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1 L
  refine ⟨C, hdisjoint, hcover, ?_⟩
  exact WilliamsonShmoys.partition_edge_accounting__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
    L C hdisjoint hcover hlocal