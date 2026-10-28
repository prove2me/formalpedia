-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension_same_vertices_20261026
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:39:34.854977+00:00
-- url     : https://prove2.me/submissions/054e8c2f-44c0-4930-b5dc-1fff6d3508ef

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) ∧
      ∀ J : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn J →
        (∀ ⦃u v : V⦄, H.Adj u v → J.Adj u v) → J = H := by
  obtain ⟨H, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn K hK
  exact ⟨H, h2, fun u v h => h1 h, fun J hd hJ => h3 J (fun u v h => hJ h) hd⟩
