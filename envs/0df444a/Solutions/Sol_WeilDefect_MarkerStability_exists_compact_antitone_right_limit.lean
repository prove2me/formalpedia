-- Prove2me | solution 1 for WeilDefect.MarkerStability.exists_compact_antitone_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T14:07:46.257153+00:00
-- url     : https://prove2.me/submissions/55785704-4dfb-428a-9767-b741327e4805

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Compactness.Compact
open Filter Set
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
theorem solution{E : Type*} [TopologicalSpace E]
    [PartialOrder E] [OrderClosedTopology E] (f : ℝ → E) (c : ℝ) (C : Set E)
    (hC : IsCompact C) (hmem : ∀ t : ℝ, c < t → f t ∈ C)
    (hanti : AntitoneOn f (Set.Ioi c)) :
    ∃ G₀ : E, G₀ ∈ C ∧ IsLUB (f '' Set.Ioi c) G₀ ∧
      Filter.Tendsto f (nhdsWithin c (Set.Ioi c)) (nhds G₀) := by
  have hev : ∀ᶠ t in nhdsWithin c (Set.Ioi c), f t ∈ C := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmem t ht
  obtain ⟨G₀, hG₀, hc⟩ := hC.exists_mapClusterPt (Filter.tendsto_principal.mpr hev)
  have hlub : ∀ y : E, MapClusterPt y (nhdsWithin c (Set.Ioi c)) f →
      IsLUB (f '' Set.Ioi c) y := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      apply isClosed_Ici.mem_of_mapClusterPt hy
      filter_upwards [Ioo_mem_nhdsGT ht] with u hu
      exact hanti hu.1 ht hu.2.le
    · intro z hz
      apply isClosed_Iic.mem_of_mapClusterPt hy
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hz (Set.mem_image_of_mem f ht)
  refine ⟨G₀, hG₀, hlub G₀ hc, ?_⟩
  apply hC.tendsto_nhds_of_unique_mapClusterPt hev
  intro y _ hy
  exact (hlub y hy).unique (hlub G₀ hc)
