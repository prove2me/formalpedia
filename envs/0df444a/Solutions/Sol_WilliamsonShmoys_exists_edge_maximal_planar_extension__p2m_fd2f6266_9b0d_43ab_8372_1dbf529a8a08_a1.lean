-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:19:27.479446+00:00
-- url     : https://prove2.me/submissions/95c397b1-6a9b-4ca8-8df0-5180f47a4f84

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N := by
  classical
  have hdown : ∀ {A B : SimpleGraph V}, A ≤ B →
      HasPlanarDrawingOn B → HasPlanarDrawingOn A := by
    intro A B hAB hB
    rcases hB with ⟨p, arc, hp, hedge, hcross⟩
    refine ⟨p, arc, hp, ?_, ?_⟩
    · intro u v huv hadj
      exact hedge u v huv (hAB hadj)
    · intro u v x y huv hxy hadj hadj' hne t ht s hs hEq
      exact hcross u v x y huv hxy (hAB hadj) (hAB hadj') hne t ht s hs hEq
  let S : Set (SimpleGraph V) := {N | M ≤ N ∧ HasPlanarDrawingOn N}
  have hSfinite : S.Finite := Set.toFinite _
  have hSnonempty : S.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hNmax⟩ := hSfinite.exists_maximal hSnonempty
  rcases hNmax with ⟨hNmem, hNmax⟩
  rcases hNmem with ⟨hMN, hNplanar⟩
  refine ⟨N, hMN, hNplanar, ?_⟩
  intro K hNK hKplanar
  exact hNmax ⟨hMN.trans hNK, hKplanar⟩ hNK