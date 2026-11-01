-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:41:31.233522+00:00
-- url     : https://prove2.me/submissions/166ccdec-06c1-41f1-9d13-596f251a9212

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_subgraph_extension__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) :
    ∃ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      (∀ ⦃u v : V⦄, U.Adj u v → W.Adj u v) ∧
      HasPlanarDrawingOn W ∧
      (∀ N : SimpleGraph V, W ≤ N → HasPlanarDrawingOn N → N ≤ W) := by
  classical
  obtain ⟨W, hUW, hW, hmax⟩ :=
    finite_maximal_subgraph_extension__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
      U HasPlanarDrawingOn hU
      (fun hGH hH => WilliamsonShmoys.planarDrawingOn_mono__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1 hGH hH)
  exact ⟨W, inferInstance, hUW, hW, hmax⟩
