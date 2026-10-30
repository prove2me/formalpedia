-- Prove2me | solution 1 for WilliamsonShmoys.connected_open_compact_metric_subtype_is_arcwise_connected__p2m_0609a56d_51e5_4256_a534_917c2073f24d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:47:36.401398+00:00
-- url     : https://prove2.me/submissions/25f1b2cb-bfa9-4aa4-bcf6-168c5c3900ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_locally_compact_open_subset_arcwise_connected__p2m_3404bc54_276a_455b_b0dc_6dc075e5ae87_a1
set_option autoImplicit false

theorem solution {X : Type} [MetricSpace X] {s : Set X} (hcompact : IsCompact s)
    [LocallyConnectedSpace s] {V : Set s} (hVopen : IsOpen V) (hVconnected : IsConnected V)
    (x : s) (hxV : x ∈ V) :
    ∀ y : s, y ∈ V → y ≠ x →
      ∃ γ : ℝ → s,
        ContinuousOn γ (Set.Icc 0 1) ∧
        Set.InjOn γ (Set.Icc 0 1) ∧
        γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ V := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hcompact
  letI : LocallyCompactSpace s := inferInstance
  exact WilliamsonShmoys.locally_compact_open_subset_arcwise_connected__p2m_3404bc54_276a_455b_b0dc_6dc075e5ae87_a1
    hVopen hVconnected x hxV