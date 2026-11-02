-- Prove2me | solution 1 for WilliamsonShmoys.drawable_planar_supergraph_maximal__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:28.759199+00:00
-- url     : https://prove2.me/submissions/029a2cec-d64c-41f6-a318-641678087e4a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by
  classical
  obtain ⟨N, hMN, hrest⟩ :=
    Finite.exists_le_maximal
      (p := fun N : SimpleGraph V => M ≤ N ∧ HasPlanarDrawingOn N)
      (a := M) ⟨le_rfl, hM⟩
  refine ⟨N, hMN, hrest.1.2, ?_⟩
  intro K hNK hK
  have hKN : K ≤ N :=
    hrest.2 ⟨hMN.trans hNK, hK⟩ hNK
  exact le_antisymm hKN hNK