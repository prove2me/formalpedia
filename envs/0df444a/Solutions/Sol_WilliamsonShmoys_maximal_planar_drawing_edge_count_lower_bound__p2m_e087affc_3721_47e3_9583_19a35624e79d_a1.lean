-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:52:55.959567+00:00
-- url     : https://prove2.me/submissions/3a3a3216-a45a-4cf0-a857-55fc0ac9bada

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_augmentation__p2m_ac724374_f88c_4ddf_bad5_42fda9b092d4_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    letI : DecidableRel S.Adj := Classical.decRel S.Adj
    3 * Fintype.card V ≤ S.edgeFinset.card + 6 := by
  letI : DecidableRel S.Adj := Classical.decRel S.Adj
  by_contra hnot
  have hlt : S.edgeFinset.card + 6 < 3 * Fintype.card V := Nat.lt_of_not_ge hnot
  obtain ⟨T, hST, hne, hT⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_augmentation__p2m_ac724374_f88c_4ddf_bad5_42fda9b092d4_a1
      S hS hcard hlt
  exact hne (hmax T hST hT)