-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:02:59.624075+00:00
-- url     : https://prove2.me/submissions/b32dfcbd-cd6a-46b3-9efa-8dadc02a9c1e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_nonempty_has_maximal__p2m_9251ca56_2f13_4506_a97b_c72b0a41465a_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ u v, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ∀ u v, K.Adj u v → H.Adj u v) := by
  classical
  let P : SimpleGraph V → Prop := fun X =>
    (∀ u v, G.Adj u v → X.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn X
  have hne : ∃ X, P X := ⟨G, by exact ⟨(fun _ _ hab => hab), hG⟩⟩
  obtain ⟨H, hHP, hmax⟩ :=
    finite_nonempty_has_maximal__p2m_9251ca56_2f13_4506_a97b_c72b0a41465a_a1 P hne
  refine ⟨H, hHP.1, hHP.2, ?_⟩
  intro K hHK hK u v huv
  have hKP : P K := by
    refine ⟨?_, hK⟩
    intro x y hxy
    exact hHK x y (hHP.1 x y hxy)
  have hKH : K ≤ H := hmax K hKP hHK
  exact hKH huv