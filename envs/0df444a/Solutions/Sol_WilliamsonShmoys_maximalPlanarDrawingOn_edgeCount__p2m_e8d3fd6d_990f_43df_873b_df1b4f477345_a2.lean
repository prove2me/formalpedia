-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarDrawingOn_edgeCount__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:20:18.340524+00:00
-- url     : https://prove2.me/submissions/1b4ff982-a923-4341-aff4-d64a5e23ba54

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarAugmentation_edgeCount__p2m_6ad3e488_df98_4029_b402_def6549b4337_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      HasPlanarDrawingOn L →
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel L.Adj := dL
       K.edgeFinset ⊆ L.edgeFinset → L.edgeFinset ⊆ K.edgeFinset)) :
    (letI : DecidableRel K.Adj := dK
     K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := dK
  obtain ⟨L, dL, hL, hKL, hcard⟩ :=
    WilliamsonShmoys.planarAugmentation_edgeCount__p2m_6ad3e488_df98_4029_b402_def6549b4337_a1 K dK hK hn
  have hLK : L.edgeFinset ⊆ K.edgeFinset := hmax L dL hL hKL
  have hEq : K.edgeFinset = L.edgeFinset := Finset.Subset.antisymm hKL hLK
  rw [hEq]
  exact hcard