-- Prove2me | solution 1 for WilliamsonShmoys.finite_hereditary_simpleGraph_maximal_extension__p2m_73d27d15_d574_4133_8bc6_c15839fd5f47_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:36:14.163942+00:00
-- url     : https://prove2.me/submissions/0775af02-a667-40fe-af4f-91da97a22461

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hP : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (N : SimpleGraph V) (hN : P N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  classical
  letI : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (by
      intro G H h
      ext u v
      exact Iff.of_eq (congrFun (congrFun h u) v))
  let admissible : SimpleGraph V → Prop := fun G => N ≤ G ∧ P G
  have hNadmissible : admissible N := ⟨le_rfl, hN⟩
  obtain ⟨K, hNK, hKmax⟩ := Finite.exists_le_maximal hNadmissible
  refine ⟨K, hNK, hKmax.1.2, ?_⟩
  intro L hKL hPL
  have hL : admissible L := ⟨hNK.trans hKL, hPL⟩
  have hLK : L ≤ K := hKmax.2 hL hKL
  exact le_antisymm hLK hKL