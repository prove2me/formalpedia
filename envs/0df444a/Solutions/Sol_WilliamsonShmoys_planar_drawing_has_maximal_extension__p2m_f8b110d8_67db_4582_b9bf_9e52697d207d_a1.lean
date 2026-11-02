-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:00:47.553683+00:00
-- url     : https://prove2.me/submissions/48d889db-1330-4fde-a1cb-21e59bc7dc5f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V, R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by
  classical
  let P : Set (SimpleGraph V) :=
    {S | R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S}
  have hfinite : P.Finite := by
    exact Set.finite_univ.subset (by
      intro S hS
      simp)
  have hnonempty : P.Nonempty := by
    exact ⟨R, le_rfl, hR⟩
  obtain ⟨S, hS⟩ := hfinite.exists_maximal hnonempty
  refine ⟨S, hS.1.1, hS.1.2, ?_⟩
  intro T hST hT
  have hTP : P T := ⟨hS.1.1.trans hST, hT⟩
  have hTS : T ≤ S := hS.2 hTP hST
  exact le_antisymm hTS hST