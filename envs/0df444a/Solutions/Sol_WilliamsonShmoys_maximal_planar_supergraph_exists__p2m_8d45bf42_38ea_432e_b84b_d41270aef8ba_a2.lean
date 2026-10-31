-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:48.71982+00:00
-- url     : https://prove2.me/submissions/89e9c25d-2755-4d98-a09b-e10f286cf1fe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W) :
    ∃ H : SimpleGraph V, W ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {H | W ≤ H ∧ HasPlanarDrawingOn H}
  have hSfinite : S.Finite := Set.toFinite S
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal ⟨W, le_rfl, hW⟩
  have hHmem : H ∈ S := hHmax.1
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ S := ⟨hHmem.1.trans hHK, hK⟩
  have hEq : H = K := hHmax.eq_of_le hKmem hHK
  exact hEq.symm