-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:55:48.616487+00:00
-- url     : https://prove2.me/submissions/20a9feaf-a09c-4ccd-a35b-33ee398d880f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a1__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, HasPlanarDrawingOn K -> T <= K -> K <= T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hcomp :=
    WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a1__p2m_d2478348_c72f_40e5_ae45_20f8d99d0e8e_a2
      T hT hV
  let K := Classical.choose hcomp
  have hprops : HasPlanarDrawingOn K ∧ T <= K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    Classical.choose_spec hcomp
  have hKT : K <= T := hmax K hprops.1 hprops.2.1
  have hEq : T = K := le_antisymm hprops.2.1 hKT
  rw [hEq]
  exact hprops.2.2