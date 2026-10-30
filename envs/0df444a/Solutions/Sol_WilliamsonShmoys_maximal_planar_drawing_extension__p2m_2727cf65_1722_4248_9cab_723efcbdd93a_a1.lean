-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_extension__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:00.480224+00:00
-- url     : https://prove2.me/submissions/b2728933-6ff9-49c0-bc7c-af346881a077

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_of_finite_partialOrder__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
import Theorems.Thm_finite_simpleGraph__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      And (LE.le G H)
        (And (HasPlanarDrawingOn H)
          (forall H' : SimpleGraph V,
            LE.le H H' -> Ne H' H -> Not (HasPlanarDrawingOn H'))) := by
  letI : Finite (SimpleGraph V) :=
    finite_simpleGraph__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
  apply Exists.elim
    (exists_maximal_of_finite_partialOrder__p2m_0e06c23e_290e_423e_a5fe_9ac4288d0e45_a2
      (fun K : SimpleGraph V => And (LE.le G K) (HasPlanarDrawingOn K))
      (Exists.intro G (And.intro le_rfl hDraw)))
  intro H h
  refine Exists.intro H (And.intro (And.left (And.left h))
    (And.intro (And.right (And.left h)) ?_))
  intro H' hHH' hne hDraw'
  exact And.right h H' hHH' hne
    (And.intro (le_trans (And.left (And.left h)) hHH') hDraw')