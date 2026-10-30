-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_784d1fda_4529_43fd_94a5_bf399d6fa183
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:34:28.528512+00:00
-- url     : https://prove2.me/submissions/0970295a-7ce6-45dd-8b3b-ff6aa0173920

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulation_completion_with_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V)
    (hmax : forall R : SimpleGraph V,
      Q.edgeSet ⊆ R.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn R ->
      R.edgeSet = Q.edgeSet) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨R, hQR, hR, hcount⟩ :=
    WilliamsonShmoys.exists_triangulation_completion_with_exact_edge_count Q hQ hV
  have hEq : R.edgeSet = Q.edgeSet := hmax R hQR hR
  rw [hEq] at hcount
  exact hcount