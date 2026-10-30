-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound_completion_aad8d6c4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:25:55.594759+00:00
-- url     : https://prove2.me/submissions/d366e8c8-4a53-4069-aafb-9e159acd3b27

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_43124a08_e00c_4a1a_ad63_e868e93f9e49
import Theorems.Thm_WilliamsonShmoys_maximal_planar_count_43124a08_e00c_4a1a_ad63_e868e93f9e49

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K.edgeSet ⊆ H.edgeSet ∧
      K.edgeSet.ncard <= H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hKH, hmax⟩ :=
    WilliamsonShmoys.planar_completion_maximal_43124a08_e00c_4a1a_ad63_e868e93f9e49
      K hK
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn H := hmax.1
  have hcount :=
    WilliamsonShmoys.maximal_planar_count_43124a08_e00c_4a1a_ad63_e868e93f9e49
      H hV hmax
  have hle : K.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hKH
  exact ⟨H, hKH, hle, hcount, hdraw⟩