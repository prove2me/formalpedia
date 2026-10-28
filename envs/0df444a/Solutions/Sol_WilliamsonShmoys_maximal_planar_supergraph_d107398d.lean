-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_d107398d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:54:45.224979+00:00
-- url     : https://prove2.me/submissions/20a2680e-8435-4759-9b97-cf7b3a1e1b3f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists H : SimpleGraph V,
      K <= H /\
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      forall J : SimpleGraph V, H <= J ->
        WilliamsonShmoys.HasPlanarDrawingOn J -> J = H := by
  classical
  let p : SimpleGraph V -> Prop :=
    fun G => K <= G /\ WilliamsonShmoys.HasPlanarDrawingOn G
  obtain ⟨H, hDec, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨K, le_rfl, hDraw⟩
  letI := hDec
  refine ⟨H, hExt.prop.1, hExt.prop.2, ?_⟩
  intro J hHJ hJ
  have hJp : p J := ⟨hExt.prop.1.trans hHJ, hJ⟩
  have hEq : H = J := (hExt.le_iff_eq hJp).mp hHJ
  exact hEq.symm