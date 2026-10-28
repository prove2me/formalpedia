-- Prove2me | solution 2 for WilliamsonShmoys.finite_simpleGraph_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:32:12.576356+00:00
-- url     : https://prove2.me/submissions/3ee41f58-d2c2-4c12-906e-cb45d4cbc7ed

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      ∀ J : SimpleGraph V, H ≤ J → P J → J = H := by
  classical
  have hfin : ({J : SimpleGraph V | K ≤ J ∧ P J}).Finite := Set.toFinite _
  obtain ⟨H, hH⟩ := hfin.exists_maximal ⟨K, le_rfl, hP⟩
  refine ⟨H, hH.prop.1, hH.prop.2, fun J hJ hPJ => ?_⟩
  exact le_antisymm (hH.2 ⟨le_trans hH.prop.1 hJ, hPJ⟩ hJ) hJ
