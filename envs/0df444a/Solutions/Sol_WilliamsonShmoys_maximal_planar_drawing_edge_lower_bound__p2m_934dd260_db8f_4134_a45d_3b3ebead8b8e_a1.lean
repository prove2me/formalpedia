-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_934dd260_db8f_4134_a45d_3b3ebead8b8e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:28:00.855592+00:00
-- url     : https://prove2.me/submissions/b95e9679-b233-4760-93cc-5f80446bf6ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_106b6c5d_3b21_4a4a_a816_9add1b924776_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    (∀ G : SimpleGraph V, K.edgeFinset ⊆ G.edgeFinset →
      HasPlanarDrawingOn G → G = K) →
      3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  classical
  intro hmaximal
  obtain ⟨G, hKG, hG, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_106b6c5d_3b21_4a4a_a816_9add1b924776_a1
      K hconn hK hcard
  have hGK : G = K := hmaximal G hKG hG
  subst G
  omega