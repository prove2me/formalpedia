-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:24.230264+00:00
-- url     : https://prove2.me/submissions/c9075424-eb6a-4deb-b4fb-c0435acf9614

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T := by
  classical
  let S : Set (SimpleGraph V) := {T | L ≤ T ∧ HasPlanarDrawingOn T}
  have hSfinite : S.Finite := Set.finite_univ.subset (Set.subset_univ S)
  have hSnonempty : S.Nonempty := ⟨L, ⟨le_rfl, hL⟩⟩
  obtain ⟨T, hTmax⟩ := hSfinite.exists_maximal hSnonempty
  have hTmem : T ∈ S := hTmax.1
  rcases hTmem with ⟨hLT, hTplanar⟩
  refine ⟨T, hLT, hTplanar, ?_⟩
  intro U hTU hUplanar
  exact hTmax.2 ⟨hLT.trans hTU, hUplanar⟩ hTU