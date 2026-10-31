-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:09:28.906759+00:00
-- url     : https://prove2.me/submissions/4b67a1a8-9636-4db2-a301-9e9b14d1003a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation__p2m_bf9be5f4_efbc_4928_a7c5_3fcb68a1a21a_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    3 * Fintype.card V - 6 ≤ S.edgeSet.ncard := by
  by_contra hBound
  have hSmall : S.edgeSet.ncard < 3 * Fintype.card V - 6 :=
    Nat.lt_of_not_ge hBound
  obtain ⟨T, hST, hNe, hT⟩ :=
    WilliamsonShmoys.planar_drawing_edge_augmentation__p2m_bf9be5f4_efbc_4928_a7c5_3fcb68a1a21a_a1
      S hS hCard hSmall
  exact hNe (hMax T hST hT)