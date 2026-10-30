-- Prove2me | solution 1 for WilliamsonShmoys.compact_locally_connected_metric_subtype_has_local_arcs__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:30.104824+00:00
-- url     : https://prove2.me/submissions/3451ae74-54af-4342-84cd-2bb469b906e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_open_compact_metric_subtype_is_arcwise_connected__p2m_0609a56d_51e5_4256_a534_917c2073f24d_a1
set_option autoImplicit false

theorem solution {X : Type} [MetricSpace X] {s : Set X} (hcompact : IsCompact s)
    (hlocal : LocallyConnectedSpace s) :
    ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U →
      ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ y ∈ V, y ≠ x → ∃ γ : ℝ → s,
          ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧
          γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by
  intro x U hU hx
  obtain ⟨V, hV, hVU⟩ := (hlocal.open_connected_basis x).mem_iff.mp (hU.mem_nhds hx)
  rcases hV with ⟨hVopen, hxV, hVconnected⟩
  refine ⟨V, hVopen, hxV, hVU, ?_⟩
  intro y hyV hyx
  obtain ⟨γ, hcont, hinj, hzero, hone, hγV⟩ :=
    WilliamsonShmoys.connected_open_compact_metric_subtype_is_arcwise_connected__p2m_0609a56d_51e5_4256_a534_917c2073f24d_a1
      hcompact hVopen hVconnected x hxV y hyV hyx
  refine ⟨γ, hcont, hinj, hzero, hone, ?_⟩
  intro t ht
  exact hVU (hγV t ht)