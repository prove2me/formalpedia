-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_edge_count__p2m_3a65eae3_5ff7_4fce_93d5_4a7db05ee858_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:37.499492+00:00
-- url     : https://prove2.me/submissions/890ea435-0877-47c9-95cf-11138dabc34a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : (K : SimpleGraph V) -> LE.le H K -> WilliamsonShmoys.HasPlanarDrawingOn K -> LE.le K H)
    (hV : LE.le 3 (Fintype.card V))
    (hconn : H.Connected) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys_planar_edge_count_upper_bound__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1 H hHplanar hV
  by_contra hne
  have hsmall : H.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  let hAug := WilliamsonShmoys_planar_edge_augmentation__p2m_2508ece6_24ff_4a9a_9901_7572a4f15f41_a1 H hHplanar hconn hV hsmall
  let K := Classical.choose hAug
  have hHK : LE.le H K := (Classical.choose_spec hAug).1
  have hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K := (Classical.choose_spec hAug).2.1
  have hnotKH : Not (LE.le K H) := (Classical.choose_spec hAug).2.2
  exact hnotKH (hmax K hHK hKplanar)