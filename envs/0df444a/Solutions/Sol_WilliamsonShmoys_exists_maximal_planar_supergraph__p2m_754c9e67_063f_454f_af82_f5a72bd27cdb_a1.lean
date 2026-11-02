-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_754c9e67_063f_454f_af82_f5a72bd27cdb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:16.659448+00:00
-- url     : https://prove2.me/submissions/2a56533b-3326-4fc9-ae0f-59f19afb3cc3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ K : SimpleGraph V, M ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  classical
  let p : SimpleGraph V → Prop := fun K => M ≤ K ∧ HasPlanarDrawingOn K
  have hMp : p M := ⟨le_rfl, hM⟩
  obtain ⟨K, _hdec, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2 ⟨M, hMp⟩
  refine ⟨K, hK.prop.1, hK.prop.2, ?_⟩
  intro L hKL hL
  have hLp : p L := ⟨hK.prop.1.trans hKL, hL⟩
  have hEq : K = L := (SimpleGraph.IsExtremal.le_iff_eq hK hLp).mp hKL
  cases hEq
  exact le_rfl