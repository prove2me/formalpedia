-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:55:45.55352+00:00
-- url     : https://prove2.me/submissions/63c17590-d632-49cc-8adc-a12717d0cabe

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

open scoped Classical in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      (∀ u v, G.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V,
        (∀ u v, L.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ∀ u v, K.Adj u v → L.Adj u v := by
  classical
  let p : SimpleGraph V → Prop := fun H =>
    (∀ u v, G.Adj u v → H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  have hGp : p G := ⟨fun _ _ h => h, hG⟩
  obtain ⟨L, _hdec, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨G, hGp⟩
  refine ⟨L, hmax.prop.1, hmax.prop.2, ?_⟩
  intro K hLK hK u v hKuv
  have hKp : p K := ⟨fun a b hab => hLK a b (hmax.prop.1 a b hab), hK⟩
  have hEq : L = K := (SimpleGraph.IsExtremal.le_iff_eq hmax hKp).mp hLK
  subst K
  exact hKuv