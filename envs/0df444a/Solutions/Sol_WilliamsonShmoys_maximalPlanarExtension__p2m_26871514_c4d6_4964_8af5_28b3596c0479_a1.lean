-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarExtension__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:41:51.247972+00:00
-- url     : https://prove2.me/submissions/8ac283ed-4c9f-4bfc-820c-a4042ee182ae

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_finite_maximal_planar_property_extension__p2m_503a8d71_6799_480d_8f3e_33232e674c95_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N ∧
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       M.edgeFinset ⊆ N.edgeFinset) ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        HasPlanarDrawingOn K →
        (letI : DecidableRel N.Adj := dN
         letI : DecidableRel K.Adj := dK
         N.edgeFinset ⊆ K.edgeFinset) →
        N = K) := by
  exact finite_maximal_planar_property_extension__p2m_503a8d71_6799_480d_8f3e_33232e674c95_a1
    (P := HasPlanarDrawingOn) M dM hM