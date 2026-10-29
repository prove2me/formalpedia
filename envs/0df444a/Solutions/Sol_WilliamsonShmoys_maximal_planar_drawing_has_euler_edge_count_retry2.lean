-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_retry2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:21:24.590975+00:00
-- url     : https://prove2.me/submissions/1c3aeb63-4e88-4022-8c0a-ddf4ac2ac83e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph_retry2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hSat : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M <= L) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hTri :=
    WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_retry2 L hV hL
  let M := Classical.choose hTri
  have hTriSpec := Classical.choose_spec hTri
  have hLM : L <= M := hTriSpec.1
  have hM : WilliamsonShmoys.HasPlanarDrawingOn M := hTriSpec.2.1
  have hcard : (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 :=
    hTriSpec.2.2
  have hML : M <= L := hSat M hLM hM
  have hEq : M = L := le_antisymm hML hLM
  simpa [hEq] using hcard