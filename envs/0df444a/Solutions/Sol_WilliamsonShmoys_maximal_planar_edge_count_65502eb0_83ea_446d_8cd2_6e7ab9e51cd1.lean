-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:13:13.7109+00:00
-- url     : https://prove2.me/submissions/16f79d86-15d2-4ebe-8002-2ac130939492

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J →
      H.edgeSet ⊆ J.edgeSet → J.edgeSet ⊆ H.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hJ, hsub, hcount⟩ :=
    WilliamsonShmoys.exists_planar_edge_count_extension H hH hV
  have hback := hmax J hJ hsub
  have hEq : H.edgeSet = J.edgeSet := Set.Subset.antisymm hsub hback
  simpa [hEq] using hcount