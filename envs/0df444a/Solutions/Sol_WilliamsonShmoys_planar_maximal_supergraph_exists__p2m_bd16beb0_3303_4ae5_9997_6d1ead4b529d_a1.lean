-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:45.491339+00:00
-- url     : https://prove2.me/submissions/9b52026d-8f94-43e9-9d21-8eaba5e66702

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_partial_order_has_maximal_above__p2m_93e678ee_21d2_4500_aea7_026ed25bc307_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      (∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        (∀ u v, N.Adj u v → P.Adj u v) → P = N) := by
  classical
  let α := {G : SimpleGraph V // WilliamsonShmoys.HasPlanarDrawingOn G ∧
    ∀ u v, M.Adj u v → G.Adj u v}
  let R : α → α → Prop := fun G H => ∀ u v, G.1.Adj u v → H.1.Adj u v
  have hRrefl : ∀ G, R G G := by
    intro G u v huv
    exact huv
  have hRtrans : ∀ G H K, R G H → R H K → R G K := by
    intro G H K hGH hHK u v huv
    exact hHK u v (hGH u v huv)
  have hRantisymm : ∀ G H, R G H → R H G → G = H := by
    intro G H hGH hHG
    apply Subtype.ext
    apply SimpleGraph.ext
    funext u v
    apply propext
    exact ⟨hGH u v, hHG u v⟩
  let a : α := ⟨M, ⟨hM, by intro u v huv; exact huv⟩⟩
  obtain ⟨b, hab, hmax⟩ :=
    WilliamsonShmoys.finite_partial_order_has_maximal_above__p2m_93e678ee_21d2_4500_aea7_026ed25bc307_a1
      R hRrefl hRtrans hRantisymm a
  refine ⟨b.1, b.2.1, ?_, ?_⟩
  · intro u v huv
    exact hab u v huv
  · intro P hP hNP
    let c : α := ⟨P, ⟨hP, by
      intro u v huv
      exact hNP u v (hab u v huv)⟩⟩
    have hbc : R b c := hNP
    have hEq := hmax c hbc
    simpa [c] using congrArg Subtype.val hEq