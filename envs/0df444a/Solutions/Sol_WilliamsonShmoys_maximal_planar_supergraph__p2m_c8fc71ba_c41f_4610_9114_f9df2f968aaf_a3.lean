-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:41.157709+00:00
-- url     : https://prove2.me/submissions/b0de4fcd-f246-45af-aa29-4082d26f7da6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_preorder_has_maximal__p2m_7d28393b_3717_42d0_a7e1_00f1426861ad_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    Exists fun P : SimpleGraph V =>
      And ((u v : V) -> N.Adj u v -> P.Adj u v)
        (And (HasPlanarDrawingOn P)
          ((Q : SimpleGraph V) ->
            ((u v : V) -> P.Adj u v -> Q.Adj u v) ->
            HasPlanarDrawingOn Q ->
            ((u v : V) -> Q.Adj u v -> P.Adj u v))) := by
  classical
  let S : Type := {P : SimpleGraph V // And (N ≤ P) (HasPlanarDrawingOn P)}
  letI : Fintype S := Fintype.ofFinite S
  obtain ⟨p, _, hmax⟩ :=
    WilliamsonShmoys.finite_preorder_has_maximal__p2m_7d28393b_3717_42d0_a7e1_00f1426861ad_a2
      (α := S) Finset.univ
      ⟨⟨N, ⟨le_rfl, hN⟩⟩, by simp⟩
  refine ⟨p.1, ?_, p.2.2, ?_⟩
  · exact p.2.1
  · intro Q hPQ hQdraw u v hQ
    let q : S := ⟨Q, ⟨by
      intro x y hxy
      exact hPQ x y (p.2.1 hxy), hQdraw⟩⟩
    have hqp : q.1 ≤ p.1 := hmax q (by simp) (show p.1 ≤ q.1 from hPQ)
    exact hqp hQ