-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:18:42.882428+00:00
-- url     : https://prove2.me/submissions/e27a5c12-5cd0-4535-bbf1-80712fe3d693

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ N : SimpleGraph V,
      (∀ u v, K.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      K.edgeFinset.card ≤ N.edgeSet.ncard ∧
      ∀ P : SimpleGraph V,
        (∀ u v, N.Adj u v → P.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        ∀ u v, P.Adj u v → N.Adj u v := by
  classical
  let good : SimpleGraph V → Prop := fun G =>
    (∀ u v, K.Adj u v → G.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hgood : ∃ G : SimpleGraph V, good G := ⟨K, fun _ _ h => h, hK⟩
  obtain ⟨N, hNmem, hNmax⟩ :=
    Set.exists_max_image {G : SimpleGraph V | good G} (fun G => G.edgeFinset.card)
      (Set.toFinite _) (by
        obtain ⟨G, hG⟩ := hgood
        exact ⟨G, by simpa using hG⟩)
  change good N at hNmem
  rcases hNmem with ⟨hKN, hNplanar⟩
  refine ⟨N, hKN, hNplanar, ?_, ?_⟩
  · calc
      K.edgeFinset.card ≤ N.edgeFinset.card :=
        Finset.card_le_card (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hKN)
      _ = N.edgeSet.ncard := by
        simpa [SimpleGraph.edgeFinset] using
          (Set.ncard_eq_toFinset_card' N.edgeSet).symm
  · intro P hNP hPplanar u v hPuv
    by_contra hNuv
    have hnotPN : ¬ P ≤ N := by
      intro hPN
      exact hNuv (hPN hPuv)
    have hne : N ≠ P := by
      intro heq
      apply hnotPN
      simpa [heq]
    have hproper : N.edgeFinset ⊂ P.edgeFinset :=
      SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr (lt_of_le_of_ne hNP hne)
    have hcard : N.edgeFinset.card < P.edgeFinset.card := Finset.card_lt_card hproper
    have hPgood : good P :=
      ⟨fun x y hKxy => hNP x y (hKN x y hKxy), hPplanar⟩
    have hmax := hNmax P (by simpa using hPgood)
    omega