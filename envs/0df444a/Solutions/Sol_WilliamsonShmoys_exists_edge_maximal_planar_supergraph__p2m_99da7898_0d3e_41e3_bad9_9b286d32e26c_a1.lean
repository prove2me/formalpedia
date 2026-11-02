-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T20:49:53.256542+00:00
-- url     : https://prove2.me/submissions/6f6aab24-6682-48e1-8af1-fdfffee5eb6b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  let P : SimpleGraph V → Prop := fun H => G ≤ H ∧ HasPlanarDrawingOn H
  have hfinite : {H : SimpleGraph V | P H}.Finite := by
    exact Set.finite_univ.subset (by
      intro H hH
      simp)
  have hnonempty : {H : SimpleGraph V | P H}.Nonempty := by
    exact ⟨G, le_rfl, hG⟩
  obtain ⟨H, hPH, hmax⟩ := hfinite.exists_maximal hnonempty
  refine ⟨H, hPH.1, hPH.2, ?_⟩
  intro K hHK hK
  have hPK : P K := ⟨hPH.1.trans hHK, hK⟩
  have hKH : K ≤ H := hmax hPK hHK
  exact le_antisymm hKH hHK
