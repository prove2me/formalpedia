-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:42:39.573864+00:00
-- url     : https://prove2.me/submissions/e32544a9-7e59-4432-ae0e-95d319fe744b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      (∀ u v, S.Adj u v → T.Adj u v) ∧
      HasPlanarDrawingOn T ∧
      (∀ u v, u ≠ v → ¬ T.Adj u v →
        ¬ ∃ U : SimpleGraph V,
          (∀ x y, T.Adj x y → U.Adj x y) ∧
          HasPlanarDrawingOn U ∧ U.Adj u v) := by
  obtain ⟨T, hST, hTm⟩ := Finite.exists_le_maximal (p := HasPlanarDrawingOn) hS
  refine ⟨T, fun u v h => hST h, hTm.prop, ?_⟩
  rintro u v - hnadj ⟨U, hTU, hU, hUadj⟩
  have hle : T ≤ U := fun x y h => hTU x y h
  exact hnadj (hTm.2 hU hle hUadj)
