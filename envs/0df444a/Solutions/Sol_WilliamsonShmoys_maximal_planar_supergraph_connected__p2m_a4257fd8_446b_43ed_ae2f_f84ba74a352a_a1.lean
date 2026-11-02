-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:45:15.657293+00:00
-- url     : https://prove2.me/submissions/11644aae-fede-4522-8025-ee73a515d648
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_extension__p2m_29b7bd89_c713_464d_96d1_5b54a307b779_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.Connected := by
  by_contra hconn
  obtain ⟨u, v, hnreach, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_29b7bd89_c713_464d_96d1_5b54a307b779_a1 H hH hconn
  let K := H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))
  have hle : H ≤ K := le_sup_left
  have heq : K = H := hmax K hle hdraw
  have huv : u ≠ v := by
    intro huv
    subst v
    exact hnreach SimpleGraph.Reachable.rfl
  have hadj : (SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj u v := by
    rw [SimpleGraph.fromEdgeSet_adj]
    simp [huv]
  have hadded : SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V)) ≤ K := le_sup_right
  have hKad : K.Adj u v := hadded hadj
  rw [heq] at hKad
  exact hnreach hKad.reachable