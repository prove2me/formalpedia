-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_repair2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:56:00.371172+00:00
-- url     : https://prove2.me/submissions/b28dceca-9282-426f-a1e1-cd5e98a25cfb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite_predicate

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V, R ≤ S ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V, S ≤ T →
        WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by
  classical
  let P : SimpleGraph V → Prop := fun S =>
    R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S
  have hP : ∃ S, P S := ⟨R, le_rfl, hR⟩
  obtain ⟨S, hS, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_of_finite_predicate P hP
  refine ⟨S, hS.1, hS.2, ?_⟩
  intro T hST hT
  exact hmax T hST ⟨le_trans hS.1 hST, hT⟩