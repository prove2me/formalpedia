-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:45.548079+00:00
-- url     : https://prove2.me/submissions/cb2f5124-cc02-4897-a1a3-f771eb1c51a7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists (fun H : SimpleGraph V =>
      And (G <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H)
          (forall K : SimpleGraph V,
            H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H))) := by
  obtain ⟨H, hGH, hHm⟩ := Finite.exists_le_maximal (p := WilliamsonShmoys.HasPlanarDrawingOn) hG
  exact ⟨H, hGH, hHm.prop, fun K hHK hK => hHm.2 hK hHK⟩
