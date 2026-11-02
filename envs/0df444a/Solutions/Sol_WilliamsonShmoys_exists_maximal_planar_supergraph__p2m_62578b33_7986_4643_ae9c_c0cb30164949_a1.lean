-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:23:17.754471+00:00
-- url     : https://prove2.me/submissions/4ab16f77-ba7f-42c6-a400-81d15516985e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by
  classical
  let p : SimpleGraph V → Prop := fun H => G ≤ H ∧ HasPlanarDrawingOn H
  have hp : ∃ H : SimpleGraph V, p H := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hDecH, hMax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2 hp
  letI : DecidableRel H.Adj := hDecH
  refine ⟨H, hMax.1.1, hMax.1.2, ?_⟩
  intro K hHK hK
  have hKp : p K := ⟨hMax.1.1.trans hHK, hK⟩
  have hEq : H = K := (SimpleGraph.IsExtremal.le_iff_eq hMax hKp).1 hHK
  exact le_of_eq hEq.symm