-- Prove2me | solution 1 for WilliamsonShmoys.joinedIn_has_injective_arc_metric__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:41:30.598087+00:00
-- url     : https://prove2.me/submissions/934c1e73-3b85-4412-bdd0-bfe2e7809275
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_arc_in_path_range__p2m_fbc04312_9eeb_4654_891c_ce7d8210aa33_a2
open unitInterval
set_option autoImplicit false

theorem solution {X : Type} [MetricSpace X] {U : Set X} {x y : X}
    (h : JoinedIn U x y) (hxy : x ≠ y) :
    ∃ γ : ℝ → X, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧
      γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by
  rcases h with ⟨p, hp⟩
  obtain ⟨γ, hγc, hγi, hγ0, hγ1, hγrange⟩ :=
    WilliamsonShmoys.exists_arc_in_path_range__p2m_fbc04312_9eeb_4654_891c_ce7d8210aa33_a2
      p hxy
  have hrange : Set.range (fun s : I => p s) ⊆ U := by
    rintro z ⟨s, rfl⟩
    exact hp s
  exact ⟨γ, hγc, hγi, hγ0, hγ1, fun t ht => hrange (hγrange t ht)⟩
