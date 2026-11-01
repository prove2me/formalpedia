-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension_of_downward_closed__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:21:25.986248+00:00
-- url     : https://prove2.me/submissions/70204a01-22aa-4fe8-bea7-02bad065301c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (C : SimpleGraph V) (hC : P C) :
    ∃ H : SimpleGraph V, C ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {G | C ≤ G ∧ P G}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨C, le_rfl, hC⟩
  obtain ⟨H, hHS, hmax⟩ := hSfin.exists_maximal hSne
  refine ⟨H, hHS.1, hHS.2, ?_⟩
  intro K hHK hPK
  have hKS : K ∈ S := ⟨hHS.1.trans hHK, hPK⟩
  have hKH : K ≤ H := hmax hKS hHK
  exact le_antisymm hKH hHK