-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:31:47.961411+00:00
-- url     : https://prove2.me/submissions/6b6a8751-f8b4-4e78-b4fc-1f5dc50f534c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      ∀ J : SimpleGraph V, H ≤ J → P J → J = H := by 
  classical
  obtain ⟨H, hKH, hmax⟩ := Finite.exists_le_maximal (p := P) hP
  exact ⟨H, hKH, hmax.1, fun J hHJ hJ => le_antisymm (hmax.2 hJ hHJ) hHJ⟩
