-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:12:01.020288+00:00
-- url     : https://prove2.me/submissions/b6ab93ab-b1bd-4050-bc0d-bfa0b3d5015b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_edgeSet_ncard_mono_of_le__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
import Theorems.Thm_planar_supergraph_edge_lower_bound__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hV : LE.le 3 (Fintype.card V))
    (hmax : ∀ M : SimpleGraph V, LE.le L M → HasPlanarDrawingOn M → LE.le M L) :
    LE.le (3 * Fintype.card V) (L.edgeSet.ncard + 6) := by
  obtain ⟨M, hLM, hM, hbound⟩ :=
    planar_supergraph_edge_lower_bound__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1 L hL hV
  have hML : LE.le M L := hmax M hLM hM
  have hcards :=
    edgeSet_ncard_mono_of_le__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1 M L hML
  omega