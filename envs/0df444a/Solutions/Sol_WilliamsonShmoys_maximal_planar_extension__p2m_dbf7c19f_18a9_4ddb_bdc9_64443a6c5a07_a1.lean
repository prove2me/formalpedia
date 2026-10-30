-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:27:23.480668+00:00
-- url     : https://prove2.me/submissions/3b8f417b-7f05-4bba-a333-81a2de2de7ba

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, LE.le K L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, LE.le L M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  let P : SimpleGraph V → Prop :=
    fun L => LE.le K L ∧ WilliamsonShmoys.HasPlanarDrawingOn L
  have hPK : P K := ⟨le_rfl, hKplanar⟩
  obtain ⟨L, hKL, hmax⟩ := Finite.exists_le_maximal hPK
  refine ⟨L, hKL, hmax.1.2, ?_⟩
  intro M hLM hMplanar
  have hML : LE.le M L := hmax.2 ⟨le_trans hKL hLM, hMplanar⟩ hLM
  exact (le_antisymm hLM hML).symm