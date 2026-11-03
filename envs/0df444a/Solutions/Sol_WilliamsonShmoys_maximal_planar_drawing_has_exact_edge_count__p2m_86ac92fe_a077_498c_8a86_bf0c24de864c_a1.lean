-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count__p2m_86ac92fe_a077_498c_8a86_bf0c24de864c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:01:16.684356+00:00
-- url     : https://prove2.me/submissions/e0507718-5582-4606-9163-18bfba16932d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_ecade84c_ffb2_4aac_a689_428692de6887_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q) :
    (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
     3 * Fintype.card V = Q.edgeFinset.card + 6) := by
  letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
  obtain ⟨R, hQR, hR, hcountR⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_ecade84c_ffb2_4aac_a689_428692de6887_a1
      Q hQ hcard
  have hRQ : R ≤ Q := hmax R hQR hR
  have hEq : R = Q := le_antisymm hRQ hQR
  subst R
  simpa using hcountR