-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_2_iii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:42.543281+00:00
-- url     : https://prove2.me/submissions/b280a2bf-14dc-4d42-881b-02d69536029d

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_graph
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_ii
import Theorems.Thm_Scott1976_DataTypesAsLattices_pair_inj


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u : Pomega) :
    graph (funOf u) = u ↔ IsGraph u := by
  constructor
  · intro heqGraph k m n hkm hkn
    have hmem : pair k m ∈ graph (funOf u) := heqGraph.symm ▸ hkm
    rcases mem_graph.mp hmem with ⟨k', m', hp, hmfun⟩
    have hk : k = k' := (pair_inj hp).1
    have hm : m = m' := (pair_inj hp).2
    have hmfun' : m ∈ funOf u (e k) := by
      rw [hk, hm]; exact hmfun
    rcases hmfun' with ⟨j, hj, hpj⟩
    have hgraph : pair n m ∈ graph (funOf u) :=
      mem_graph.mpr ⟨n, m, rfl, ⟨j, subset_trans hj hkn, hpj⟩⟩
    exact heqGraph ▸ hgraph
  · intro hu
    apply subset_antisymm
    · intro p hp
      rcases hp with ⟨n, m, rfl, ⟨k, hk, hkm⟩⟩
      exact hu hkm hk
    · exact theorem_1_2_ii u
end Scott1976.DataTypesAsLattices
