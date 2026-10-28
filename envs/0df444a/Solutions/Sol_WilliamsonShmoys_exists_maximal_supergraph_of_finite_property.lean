-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_property
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:31:46.663455+00:00
-- url     : https://prove2.me/submissions/af1d7b6e-e267-4268-833e-7608919e74cd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ P L ∧
        ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by 
  classical
  obtain ⟨H, hKH, hmax⟩ := Finite.exists_le_maximal (p := P) hK
  exact ⟨H, hKH, hmax.1, fun M h hM => hmax.2 hM h⟩
