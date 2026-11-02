-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:01:53.626805+00:00
-- url     : https://prove2.me/submissions/0e20e770-0d75-4830-91c1-81a03684941e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K ≤ L ∧ L ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn L) := by
  intro h
  let K : SimpleGraph (Fin 0) := ⊥
  have hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K := by
    refine ⟨(fun x : Fin 0 => Fin.elim0 x), (fun u v t => Fin.elim0 u), ?_, ?_, ?_⟩
    · intro u v
      exact Fin.elim0 u
    · intro u v huv hadj
      exact Fin.elim0 u
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      exact Fin.elim0 u
  have hDisconnected : ¬ K.Connected := by
    intro hConnected
    rcases hConnected.nonempty with ⟨v⟩
    exact Fin.elim0 v
  rcases h K hDrawing hDisconnected with ⟨L, hSub, hNe, hLDrawing⟩
  have hEq : L = K := by
    ext u v
    exact Fin.elim0 u
  exact hNe hEq