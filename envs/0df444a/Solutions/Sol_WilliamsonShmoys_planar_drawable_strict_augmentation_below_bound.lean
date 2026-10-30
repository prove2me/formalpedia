-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_strict_augmentation_below_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:12:56.29552+00:00
-- url     : https://prove2.me/submissions/074ff71f-3ca6-48fd-981d-253b97158621

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_finite_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V)
    (hlt : R.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ S : SimpleGraph V,
      (∀ {u v}, R.Adj u v → S.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧ S ≠ R := by
  obtain ⟨S, hRS, hdrawS, hmax⟩ :=
    WilliamsonShmoys.exists_finite_maximal_drawable_supergraph R hdraw
  have hcard := WilliamsonShmoys.finite_maximal_drawable_edge_count S hdrawS hV hmax
  refine ⟨S, hRS, hdrawS, ?_⟩
  intro heq
  subst S
  rw [hcard] at hlt
  exact (Nat.lt_irrefl _ hlt)