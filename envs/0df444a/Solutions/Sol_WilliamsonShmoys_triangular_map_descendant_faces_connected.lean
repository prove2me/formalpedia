-- Prove2me | solution 1 for WilliamsonShmoys.triangular_map_descendant_faces_connected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T22:41:46.539118+00:00
-- url     : https://prove2.me/submissions/6e98578c-68dc-40d2-a495-124bbf307275

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Theorems.Thm_WilliamsonShmoys_descendant_vertex_set_one_edge_cut
import Theorems.Thm_WilliamsonShmoys_triangular_map_one_edge_cut_faces_connected

set_option autoImplicit false

 theorem solution
    {V F : Type} [Fintype V] [Fintype F]
    {H : SimpleGraph V} (M : WilliamsonShmoys.TriangularMap H F)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree)
    (root : V) (Q : (v : V) → R.Walk root v)
    (hQ : ∀ v, (Q v).IsPath) (v : V) :
    ((M.cotree R).induce
      {f : F | ∃ i : Fin 3, v ∈ (Q (M.corner f i)).support}).Connected := by
  let S : Set V := {x | v ∈ (Q x).support}
  have hdesc := WilliamsonShmoys.descendant_vertex_set_one_edge_cut
    R hR root Q hQ v
  rcases hdesc with ⟨hne, hconn, hcut⟩
  exact WilliamsonShmoys.triangular_map_one_edge_cut_faces_connected
    M R hRH hR S hne hconn hcut