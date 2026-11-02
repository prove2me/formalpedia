-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:52.700306+00:00
-- url     : https://prove2.me/submissions/0b39388c-dc90-4169-b0c0-9491d406ea4d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q →
        WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by
  classical
  let s : Set (SimpleGraph V) :=
    {P | N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P}
  have hs_nonempty : s.Nonempty := ⟨N, le_rfl, hN⟩
  have hs_finite : s.Finite :=
    Set.Finite.subset Set.finite_univ (by
      intro P hP
      exact Set.mem_univ P)
  obtain ⟨P, hPmem, hPmax⟩ := hs_finite.exists_maximal hs_nonempty
  rcases hPmem with ⟨hNP, hPplanar⟩
  refine ⟨P, hNP, SimpleGraph.Connected.mono hNP hconn, hPplanar, ?_⟩
  intro Q hPQ hQplanar
  have hQmem : Q ∈ s := ⟨hNP.trans hPQ, hQplanar⟩
  exact le_antisymm (hPmax hQmem hPQ) hPQ