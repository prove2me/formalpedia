-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_73871160_1692_421c_aaf6_a7b2b6384c07_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:04.039358+00:00
-- url     : https://prove2.me/submissions/6cf201ea-2d81-4474-824c-0f200b5cc682

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_same_vertices__p2m_5db777ea_26b2_4b9c_844f_64ae8eedcb74_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hUplanar, hUcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_same_vertices__p2m_5db777ea_26b2_4b9c_844f_64ae8eedcb74_a1
      T hT hV
  have hUT : U ≤ T := hmax U hTU hUplanar
  have hEq : T = U := le_antisymm hTU hUT
  subst U
  exact hUcount