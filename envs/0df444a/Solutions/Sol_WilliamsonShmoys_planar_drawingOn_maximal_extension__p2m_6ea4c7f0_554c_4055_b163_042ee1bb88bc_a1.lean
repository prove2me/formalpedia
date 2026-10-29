-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_extension__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:17:32.973291+00:00
-- url     : https://prove2.me/submissions/db98b0cb-0340-4e69-8b19-45bc064d1dae

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        H.edgeSet = K.edgeSet := by
  classical
  let Q : SimpleGraph V → Prop := fun K => G ≤ K ∧ HasPlanarDrawingOn K
  obtain ⟨H, hGH, hmax⟩ :=
    Finite.exists_le_maximal (p := Q) (a := G) ⟨le_rfl, hG⟩
  have hGHset : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hGH
  refine ⟨H, hGHset, hmax.1.2, ?_⟩
  intro K hHKset hK
  have hHK : H ≤ K := SimpleGraph.edgeSet_subset_edgeSet.mp hHKset
  have hGK : G ≤ K := le_trans hGH hHK
  have hKH : K ≤ H := hmax.2 ⟨hGK, hK⟩ hHK
  have hEq : K = H := le_antisymm hKH hHK
  exact congrArg SimpleGraph.edgeSet hEq.symm