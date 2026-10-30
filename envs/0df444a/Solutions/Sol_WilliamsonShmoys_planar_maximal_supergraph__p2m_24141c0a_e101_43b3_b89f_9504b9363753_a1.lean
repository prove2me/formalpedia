-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:44.944067+00:00
-- url     : https://prove2.me/submissions/806bdd9e-3114-4cd0-976a-40dc748c0d9b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_partial_order_maximal_member_above__p2m_ecf2311e_b31c_4b92_8561_385ce369da7c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
        ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → L = H := by
  classical
  let P : SimpleGraph V → Prop := fun K => G ≤ K ∧ HasPlanarDrawingOn K
  obtain ⟨H, hGH, hPH, hmax⟩ :=
    finite_partial_order_maximal_member_above__p2m_ecf2311e_b31c_4b92_8561_385ce369da7c_a1
      P ⟨le_rfl, hplanar⟩
  rcases hPH with ⟨_, hplanarH⟩
  refine ⟨H, hGH, hplanarH, ?_⟩
  intro L hHL hplanarL
  exact hmax L ⟨le_trans hGH hHL, hplanarL⟩ hHL