-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_when_sparse_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:58:45.206831+00:00
-- url     : https://prove2.me/submissions/87d380aa-a29a-4c25-997b-5f43f291ab72

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_729fc1e5
import Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_maximal_planar_729fc1e5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hsparse : Q.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ R ≠ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn R := by
  obtain ⟨R, hQR, hR, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_729fc1e5 Q hQ
  have hcount :=
    WilliamsonShmoys.edge_count_eq_of_maximal_planar_729fc1e5
      R hV hR hmax
  have hne : R ≠ Q := by
    intro hEq
    subst R
    omega
  exact ⟨R, hQR, hne, hR⟩