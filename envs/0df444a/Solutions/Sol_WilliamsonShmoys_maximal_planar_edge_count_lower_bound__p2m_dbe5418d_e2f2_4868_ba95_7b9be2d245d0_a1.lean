-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:14:31.275229+00:00
-- url     : https://prove2.me/submissions/bd86ab5b-8882-4e86-bfdd-cdd59369b097

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count__p2m_00590216_3bdf_4c63_b52e_9e355ea90f1e_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : forall L : SimpleGraph V, LE.le K L -> WilliamsonShmoys.HasPlanarDrawingOn L -> LE.le L K)
    (hV : Nat.le 3 (Fintype.card V)) : Nat.le (3 * Fintype.card V - 6) K.edgeSet.ncard := by
  let hcompletion :=
    WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_00590216_3bdf_4c63_b52e_9e355ea90f1e_a1 K hKplanar hV
  let L := Classical.choose hcompletion
  have hL := Classical.choose_spec hcompletion
  have hKL : LE.le K L := hL.1
  have hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L := hL.2.1
  have hLcount : 3 * Fintype.card V - 6 = L.edgeSet.ncard := hL.2.2
  have hLK : LE.le L K := hKmax L hKL hLplanar
  have hEq : K = L := le_antisymm hKL hLK
  simpa [hEq] using hLcount.le