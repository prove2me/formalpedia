-- Prove2me | solution 2 for WilliamsonShmoys.drawable_planar_supergraph_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:24:01.394532+00:00
-- url     : https://prove2.me/submissions/c4d6f8f2-d235-4455-9a81-9efd2399433d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_in_finite_set

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ W : SimpleGraph V, HasPlanarDrawingOn W ∧
      (∀ u v, G.Adj u v → W.Adj u v) ∧
      (∀ X : SimpleGraph V, HasPlanarDrawingOn X →
        (∀ u v, W.Adj u v → X.Adj u v) →
        ∀ u v, X.Adj u v → W.Adj u v) := by
  classical
  let S : Set (SimpleGraph V) :=
    {W | HasPlanarDrawingOn W ∧ ∀ u v, G.Adj u v → W.Adj u v}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := by
    refine ⟨G, hG, ?_⟩
    intro u v huv
    exact huv
  obtain ⟨W, hW, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_simpleGraph_in_finite_set S hSfin hSne
  refine ⟨W, hW.1, hW.2, ?_⟩
  intro X hX hWX u v hXuv
  have hXS : X ∈ S := by
    refine ⟨hX, ?_⟩
    intro a b hab
    exact hWX a b (hW.2 a b hab)
  exact hmax X hXS hWX u v hXuv