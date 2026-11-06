-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_bounds_large__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:31:56.692708+00:00
-- url     : https://prove2.me/submissions/adef97d5-d135-471e-9786-21f019f3a536

-- ID: 6a70bc9e-bafc-44c9-9e52-5ddfb96b8782 | NAME: WilliamsonShmoys.component_edge_bounds_large__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1 | 未本地编译验证
import Mathlib

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLocal : ∀ (S : Finset V), 3 ≤ S.card → (L.induce (↑S : Set V)).Connected → (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) (c : L.ConnectedComponent) (hlarge : 3 ≤ (SimpleGraph.ConnectedComponent.supp c).ncard) : (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard + 6 ≤ 3 * (SimpleGraph.ConnectedComponent.supp c).ncard := by
  classical
  let S : Finset V := (SimpleGraph.ConnectedComponent.supp c).toFinset
  have hS_eq : (↑S : Set V) = SimpleGraph.ConnectedComponent.supp c := by
    change ((SimpleGraph.ConnectedComponent.supp c).toFinset : Set V) = _
    exact Set.coe_toFinset _
  have hScard : S.card = (SimpleGraph.ConnectedComponent.supp c).ncard := by
    change ((SimpleGraph.ConnectedComponent.supp c).toFinset).card =
      (SimpleGraph.ConnectedComponent.supp c).ncard
    exact (Set.ncard_eq_toFinset_card' (SimpleGraph.ConnectedComponent.supp c)).symm
  have hS3 : 3 ≤ S.card := by omega
  have hconn0 : (L.induce (SimpleGraph.ConnectedComponent.supp c)).Connected := by
    simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using
      (SimpleGraph.ConnectedComponent.connected_toSimpleGraph c)
  have hconn : (L.induce (↑S : Set V)).Connected := by
    rw [hS_eq]
    exact hconn0
  have h := hLocal S hS3 hconn
  rw [hS_eq] at h
  rw [hScard] at h
  exact h
