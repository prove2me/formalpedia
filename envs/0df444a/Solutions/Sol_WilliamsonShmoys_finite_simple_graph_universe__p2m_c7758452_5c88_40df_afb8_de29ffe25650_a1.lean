-- Prove2me | solution 1 for WilliamsonShmoys.finite_simple_graph_universe__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:46.36749+00:00
-- url     : https://prove2.me/submissions/83c90a9a-777e-4653-89b3-0fb0f3803acc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] :
    (Set.univ : Set (SimpleGraph V)).Finite := by
  classical
  let encode : SimpleGraph V → V → V → Bool :=
    fun G u v => decide (G.Adj u v)
  have hencode : Function.Injective encode := by
    intro G H h
    apply SimpleGraph.ext
    funext u v
    apply propext
    have huv : decide (G.Adj u v) = decide (H.Adj u v) :=
      congrFun (congrFun h u) v
    constructor
    · intro hG
      have htrue : decide (G.Adj u v) = true := by simp [hG]
      rw [huv] at htrue
      exact of_decide_eq_true htrue
    · intro hH
      have htrue : decide (H.Adj u v) = true := by simp [hH]
      rw [← huv] at htrue
      exact of_decide_eq_true htrue
  letI : Finite (SimpleGraph V) := Finite.of_injective encode hencode
  exact Set.toFinite _