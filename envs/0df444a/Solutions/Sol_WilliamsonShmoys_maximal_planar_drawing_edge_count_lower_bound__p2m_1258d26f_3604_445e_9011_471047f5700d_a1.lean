-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_1258d26f_3604_445e_9011_471047f5700d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:14.901827+00:00
-- url     : https://prove2.me/submissions/02ab8f33-96a0-455d-8964-fab44e028ae3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_augmentation_edge_bound__p2m_c7182b6b_7db6_44e9_8732_a23951984627_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> LE.le L K)
    (hV : LE.le 3 (Fintype.card V)) :
    LE.le (3 * Fintype.card V) (K.edgeSet.ncard + 6) := by
  obtain ⟨L, hKL, hL, hbound⟩ :=
    planar_drawing_augmentation_edge_bound__p2m_c7182b6b_7db6_44e9_8732_a23951984627_a1
      K hK hV
  have hLK : LE.le L K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  rw [hEq] at hbound
  exact hbound