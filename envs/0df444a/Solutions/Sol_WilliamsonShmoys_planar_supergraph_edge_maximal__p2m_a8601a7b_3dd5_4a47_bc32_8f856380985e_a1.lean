-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:37.969753+00:00
-- url     : https://prove2.me/submissions/e3078620-3607-4d33-b9db-6c3c24ba6191

import Theorems.Thm_WilliamsonShmoys_finite_graph_extension_maximal__p2m_eacf956f_cefb_4210_bf9e_9cc0b6fb5cbc_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact WilliamsonShmoys.finite_graph_extension_maximal__p2m_eacf956f_cefb_4210_bf9e_9cc0b6fb5cbc_a1
    K (fun G => HasPlanarDrawingOn G) (fun G => G.edgeSet.ncard) hK
    (by
      intro G J hGJ
      exact Set.ncard_mono (SimpleGraph.edgeSet_mono hGJ))