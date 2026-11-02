-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_extension_on_same_vertices__p2m_45533a44_b035_4e47_8a66_77352d0d9780_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:01.976104+00:00
-- url     : https://prove2.me/submissions/7bc7b247-3918-4b84-960e-a9ad902488d1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      K.edgeSet.ncard ≤ L.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  let p : SimpleGraph V → Prop :=
    fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hKp : p K := ⟨le_rfl, hK⟩
  obtain ⟨L, _instL, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := p)).2 ⟨K, hKp⟩
  have hKL : K ≤ L := hExt.1.1
  have hPlanarL : WilliamsonShmoys.HasPlanarDrawingOn L := hExt.1.2
  refine ⟨L, hKL, Set.ncard_mono (SimpleGraph.edgeSet_mono hKL), hPlanarL, ?_⟩
  intro M hLM hPlanarM
  have hKM : K ≤ M := hKL.trans hLM
  have hMp : p M := ⟨hKM, hPlanarM⟩
  have hEq : L = M := (SimpleGraph.IsExtremal.le_iff_eq hExt hMp).mp hLM
  exact hEq.symm