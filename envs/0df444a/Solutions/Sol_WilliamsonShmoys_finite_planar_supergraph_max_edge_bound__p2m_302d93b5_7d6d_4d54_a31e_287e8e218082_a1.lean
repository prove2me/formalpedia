-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_supergraph_max_edge_bound__p2m_302d93b5_7d6d_4d54_a31e_287e8e218082_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:01:39.586056+00:00
-- url     : https://prove2.me/submissions/463830c2-f93c-469c-983b-7beed11e228c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V, K ≤ J → HasPlanarDrawingOn J →
          J.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let Feasible : Type := {G : SimpleGraph V // K ≤ G ∧ HasPlanarDrawingOn G}
  letI : Nonempty Feasible := ⟨⟨K, le_rfl, hK⟩⟩
  letI : Fintype Feasible := Fintype.ofFinite Feasible
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image Finset.univ
      (fun G : Feasible => G.1.edgeSet.ncard)
      (Finset.univ_nonempty)
  refine ⟨H.1, H.2.1, H.2.2, ?_⟩
  intro J hKJ hJ
  have hJmem : (⟨J, hKJ, hJ⟩ : Feasible) ∈ Finset.univ := Finset.mem_univ _
  exact hHmax ⟨J, hKJ, hJ⟩ hJmem