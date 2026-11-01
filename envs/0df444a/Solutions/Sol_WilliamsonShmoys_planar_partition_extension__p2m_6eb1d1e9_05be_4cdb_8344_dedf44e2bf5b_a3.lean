-- Prove2me | solution 1 for WilliamsonShmoys.planar_partition_extension__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:49:07.36403+00:00
-- url     : https://prove2.me/submissions/80d3d6e6-914d-4e70-ad68-a861e5da4ba1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_of_not_reachable__p2m_a749677c_638f_4aa9_a97a_7bf2c9f27f0d_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (A : Set V)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hcross : ∀ ⦃u v : V⦄, u ∈ A → v ∈ Aᶜ → ¬ M.Adj u v)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ ¬ N ≤ M := by
  rcases hA with ⟨u, hu⟩
  rcases hAc with ⟨v, hv⟩
  have hstay : ∀ {w : V}, M.Reachable u w → w ∈ A := by
    intro w hreach
    have hrt : Relation.ReflTransGen M.Adj u w :=
      (M.reachable_iff_reflTransGen u w).mp hreach
    clear hreach
    induction hrt with
    | refl => exact hu
    | tail _ hadj ih =>
        by_contra hw
        exact (hcross ih (by simpa using hw) hadj).elim
  have hsep : ¬ M.Reachable u v := by
    intro hreach
    exact hv (hstay hreach)
  exact WilliamsonShmoys.planar_drawing_add_edge_of_not_reachable__p2m_a749677c_638f_4aa9_a97a_7bf2c9f27f0d_a1
    M u v hsep hM
