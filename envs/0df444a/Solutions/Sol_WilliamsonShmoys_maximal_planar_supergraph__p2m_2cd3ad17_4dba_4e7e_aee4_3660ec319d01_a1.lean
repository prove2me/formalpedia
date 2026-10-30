-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_2cd3ad17_4dba_4e7e_aee4_3660ec319d01_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:39:07.049548+00:00
-- url     : https://prove2.me/submissions/0352e0d4-8610-48e7-bdb2-6352d4d8d7fa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  classical
  let P : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hPK : P K := ⟨le_rfl, hK⟩
  obtain ⟨L, hKL, hLmax⟩ := Finite.exists_le_maximal (p := P) hPK
  refine ⟨L, hKL, hLmax.prop.2, ?_⟩
  intro M hLM hMplanar
  have hML : M ≤ L := by
    by_contra hnot
    exact hLmax.not_prop_of_gt (lt_of_le_not_ge hLM hnot)
      ⟨hKL.trans hLM, hMplanar⟩
  exact le_antisymm hML hLM