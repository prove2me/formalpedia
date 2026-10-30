-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_from_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:32.125396+00:00
-- url     : https://prove2.me/submissions/db28553e-dc3f-46dd-8b3e-3aaa8a7a7b4d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension__p2m_3750f754_8764_46ea_8741_399ac1e39bbe_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 0 < Fintype.card V)
    (bridgeStep : ∀ (G : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G →
      (¬ ∀ u v, Relation.ReflTransGen G.Adj u v) →
      ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∃ u v, ¬ Relation.ReflTransGen G.Adj u v ∧ H.Adj u v)
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_finite_maximal_extension__p2m_3750f754_8764_46ea_8741_399ac1e39bbe_a1 G hG
  by_cases hconn : ∀ u v, Relation.ReflTransGen H.Adj u v
  · exact ⟨H, hGH, hconn, hH⟩
  · obtain ⟨K, hHK, hK, u, v, hnot, huv⟩ := bridgeStep H hH hconn
    have hKH : K ≤ H := hmax K hHK hK
    exact False.elim (hnot (Relation.ReflTransGen.single (hKH huv)))