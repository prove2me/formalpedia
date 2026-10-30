-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_card_planar_supergraph__p2m_3e744d16_fd12_4405_889b_d7d7bae50b90_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:45:52.432673+00:00
-- url     : https://prove2.me/submissions/2dfecdb2-dec7-48f8-8a70-5886a435bc7a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_predicate_has_maximum__p2m_732ef142_c02d_434e_9b88_adbee85d4bda_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
        L ≤ M →
        Nat.card {e : Sym2 V // e ∈ M.edgeSet} ≤
          Nat.card {e : Sym2 V // e ∈ L.edgeSet} := by
  classical
  obtain ⟨L, hL, hmax⟩ :=
    finite_predicate_has_maximum__p2m_732ef142_c02d_434e_9b88_adbee85d4bda_a1
      (α := SimpleGraph V)
      (P := fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      (f := fun G => Nat.card {e : Sym2 V // e ∈ G.edgeSet})
      ⟨K, le_rfl, hDraw⟩
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hKM hMDrawing hLM
  exact hmax M ⟨hKM, hMDrawing⟩