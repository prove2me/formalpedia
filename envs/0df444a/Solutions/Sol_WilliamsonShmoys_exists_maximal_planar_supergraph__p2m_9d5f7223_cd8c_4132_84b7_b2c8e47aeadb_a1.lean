-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:39.784242+00:00
-- url     : https://prove2.me/submissions/30d18be9-2753-4cdc-b84f-887a848826ab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
import Theorems.Thm_WilliamsonShmoys_proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
import Theorems.Thm_WilliamsonShmoys_edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      And (forall u v, G.Adj u v -> H.Adj u v)
      (And (WilliamsonShmoys.HasPlanarDrawingOn H)
        (forall K : SimpleGraph V,
          (forall u v, H.Adj u v -> K.Adj u v) ->
          WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)) := by
  let R : SimpleGraph V -> SimpleGraph V -> Prop :=
    fun H K => forall u v, H.Adj u v -> K.Adj u v
  let P : SimpleGraph V -> Prop :=
    fun H => And (forall u v, G.Adj u v -> H.Adj u v)
      (WilliamsonShmoys.HasPlanarDrawingOn H)
  let m : SimpleGraph V -> Nat := fun H => H.edgeSet.ncard
  have hbound : forall H : SimpleGraph V, P H -> m H <= Fintype.card (Sym2 V) := by
    intro H hH
    exact WilliamsonShmoys.edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3 H
  have hstrict : forall H K : SimpleGraph V, R H K -> Not (H = K) -> m H < m K := by
    intro H K hHK hne
    exact WilliamsonShmoys.proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
      H K hHK hne
  have hchoose :=
    WilliamsonShmoys.finite_predicate_maximal_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
      R m (Fintype.card (Sym2 V)) P hbound hstrict G
      (And.intro (by intro u v huv; exact huv) hG)
  let H := Classical.choose hchoose
  have hPHmax : And (P H) (forall K : SimpleGraph V, R H K -> P K -> K = H) :=
    Classical.choose_spec hchoose
  have hGH : forall u v, G.Adj u v -> H.Adj u v := hPHmax.left.left
  have hPlanarH : WilliamsonShmoys.HasPlanarDrawingOn H := hPHmax.left.right
  refine Exists.intro H (And.intro hGH (And.intro hPlanarH ?_))
  intro K hHK hPlanarK
  apply hPHmax.right K hHK
  exact And.intro
    (by
      intro u v huv
      exact hHK u v (hGH u v huv))
    hPlanarK