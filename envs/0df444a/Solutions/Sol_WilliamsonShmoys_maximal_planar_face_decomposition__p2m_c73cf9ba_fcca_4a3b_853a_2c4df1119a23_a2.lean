-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:39:00.078415+00:00
-- url     : https://prove2.me/submissions/8dbbb278-e53f-48ff-ba39-70e8f4bb7a5c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hUpper :=
    WilliamsonShmoys.planar_simple_edge_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
      K hK hCard
  have hEq : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    apply Nat.le_antisymm hUpper
    by_contra hNot
    have hStrict : K.edgeSet.ncard + 6 < 3 * Fintype.card V := Nat.lt_of_not_ge hNot
    obtain ⟨L, hKL, hL⟩ :=
      WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
        K hK hCard hStrict
    have hLK : K ≤ L := le_of_lt hKL
    have hSame : L = K := hMax L hLK hL
    exact (ne_of_lt hKL) hSame.symm
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega