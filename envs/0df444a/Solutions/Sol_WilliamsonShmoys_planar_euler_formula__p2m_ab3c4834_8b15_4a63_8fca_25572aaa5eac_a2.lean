-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_formula__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T22:43:35.259616+00:00
-- url     : https://prove2.me/submissions/08460777-5cac-477b-83b2-9da346f581d0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hconn : M.Connected) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  letI : Fintype (↑M.edgeSet) := M.fintypeEdgeSet
  have hle : Fintype.card V ≤ M.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
      (SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn)
  refine ⟨M.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  have hbound : Fintype.card V ≤ M.edgeFinset.card + 2 := by omega
  exact Nat.add_sub_of_le hbound
