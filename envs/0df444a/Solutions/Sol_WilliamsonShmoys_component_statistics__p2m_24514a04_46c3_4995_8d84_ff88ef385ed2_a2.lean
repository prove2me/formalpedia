-- Prove2me | solution 1 for WilliamsonShmoys.component_statistics__p2m_24514a04_46c3_4995_8d84_ff88ef385ed2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:49:55.593272+00:00
-- url     : https://prove2.me/submissions/3ec599b8-7309-486e-b016-963c8450c59b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_induce__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hconnected : ∀ {U : Type} [Fintype U] [LinearOrder U]
      (N : SimpleGraph U) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N → N.Connected → 3 ≤ Fintype.card U →
      N.edgeFinset.card ≤ 3 * Fintype.card U - 6)
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M) :
    ∃ parts : List (Nat × Nat),
      (parts.map Prod.fst).sum = Fintype.card V ∧
      (parts.map Prod.snd).sum = M.edgeFinset.card ∧
      ∀ p ∈ parts,
        (3 ≤ p.1 → p.2 ≤ 3 * p.1 - 6) ∧
        (p.1 < 3 → p.2 ≤ p.1) := by
  classical
  letI : DecidableRel M.Adj := dM
  obtain ⟨components, hunique, hvertices, hedges, hcomp_connected, hsmall⟩ :=
    WilliamsonShmoys.connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1 M
  let pairs : List (Nat × Nat) := components.toList.map (fun (W : Finset V) =>
    (W.card, (M.induce (W : Set V)).edgeSet.ncard))
  have hvertices_list : (pairs.map Prod.fst).sum = Fintype.card V := by
    simpa [pairs, List.map_map] using hvertices.symm
  have hedges_list : (pairs.map Prod.snd).sum = M.edgeFinset.card := by
    have hsum : (pairs.map Prod.snd).sum = M.edgeSet.ncard := by
      simpa [pairs, List.map_map] using hedges.symm
    calc
      (pairs.map Prod.snd).sum = M.edgeSet.ncard := hsum
      _ = M.edgeFinset.card := by
        simp [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  refine ⟨pairs, hvertices_list, hedges_list, ?_⟩
  intro p hp
  rcases List.mem_map.mp hp with ⟨W, hW, rfl⟩
  have hW' : W ∈ components := Finset.mem_toList.mp hW
  letI : DecidableRel (M.induce (W : Set V)).Adj := fun x y => dM x.val y.val
  have hdraw : HasPlanarDrawingOn (M.induce (W : Set V)) :=
    WilliamsonShmoys.planar_drawingOn_induce__p2m_bfb48bad_a912_467d_9a83_873a376cfdde_a1 M hM W
  have hsmall_edge : W.card < 3 → (M.induce (W : Set V)).edgeSet.ncard ≤ W.card := by
    intro hlt
    have hs := hsmall W hW' hlt
    omega
  constructor
  · intro hlarge
    have hcard : 3 ≤ Fintype.card {v // v ∈ (W : Set V)} := by
      simpa using hlarge
    have hb := hconnected (M.induce (W : Set V))
      (fun x y => dM x.val y.val) hdraw (hcomp_connected W hW') hcard
    simpa [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hb
  · intro hlt
    exact hsmall_edge hlt
