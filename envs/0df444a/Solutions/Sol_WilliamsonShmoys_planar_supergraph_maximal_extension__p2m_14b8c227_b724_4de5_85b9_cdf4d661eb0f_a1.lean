-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_14b8c227_b724_4de5_85b9_cdf4d661eb0f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:38.305411+00:00
-- url     : https://prove2.me/submissions/67fe9358-2159-4656-9e6c-2fe5ced5bc4a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_predicate_has_maximal_above__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P := by
  classical
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simpleGraph__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
  let S : SimpleGraph V → Prop := fun G => N ≤ G ∧ HasPlanarDrawingOn G
  have hS : S N := ⟨le_rfl, hN⟩
  obtain ⟨P, hP, hNP, hmax⟩ :=
    finite_predicate_has_maximal_above__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
      S N hS
  refine ⟨P, hNP, hP.2, ?_⟩
  intro Q hPQ hQ
  exact hmax Q ⟨le_trans hNP hPQ, hQ⟩ hPQ