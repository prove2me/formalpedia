-- Prove2me | solution 1 for WilliamsonShmoys.locally_compact_open_subset_arcwise_connected__p2m_3404bc54_276a_455b_b0dc_6dc075e5ae87_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:19:01.706993+00:00
-- url     : https://prove2.me/submissions/b0c6ea90-ced8-4809-a746-e249550dea11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_locally_compact_locally_connected_metric_is_locally_path_connected__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
import Theorems.Thm_WilliamsonShmoys_joinedIn_has_injective_arc_metric__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
set_option autoImplicit false

theorem solution {X : Type} [MetricSpace X] [LocallyCompactSpace X]
    [LocallyConnectedSpace X] {U : Set X} (hUopen : IsOpen U)
    (hUconnected : IsConnected U) (x : X) (hxU : x ∈ U) :
    ∀ y : X, y ∈ U → y ≠ x →
      ∃ γ : ℝ → X, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧
        γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by
  letI : LocallyPathConnectedSpace X :=
    WilliamsonShmoys.locally_compact_locally_connected_metric_is_locally_path_connected__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
  have hUpath : IsPathConnected U := hUopen.isConnected_iff_isPathConnected.mp hUconnected
  intro y hyU hne
  exact WilliamsonShmoys.joinedIn_has_injective_arc_metric__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
    (hUpath.joinedIn x hxU y hyU) hne.symm