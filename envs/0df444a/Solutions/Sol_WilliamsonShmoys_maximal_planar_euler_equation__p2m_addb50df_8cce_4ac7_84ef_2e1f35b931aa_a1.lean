-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_equation__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:18:10.428004+00:00
-- url     : https://prove2.me/submissions/dfd79b23-bc75-4ff4-92cb-0c71cbc35e14

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → H ≤ L → L = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2) := by
  classical
  have hb :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
      H hcard hdraw (by
        intro L hle hd
        apply hmax L hd
        intro u v huv
        exact hle huv)
  have hn : Fintype.card V ≤ H.edgeFinset.card + 2 := by omega
  exact ⟨H.edgeFinset.card + 2 - Fintype.card V, by omega⟩
