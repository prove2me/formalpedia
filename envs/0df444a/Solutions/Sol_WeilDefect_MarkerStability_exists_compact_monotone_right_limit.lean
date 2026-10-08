-- Prove2me | solution 1 for WeilDefect.MarkerStability.exists_compact_monotone_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T13:13:31.752998+00:00
-- url     : https://prove2.me/submissions/e8efe117-113d-4e20-bbf9-a3a93b635d9e

import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
open Filter Set
noncomputable section
theorem solution{E : Type*} [TopologicalSpace E]
    [PartialOrder E] [OrderClosedTopology E] (f : ℝ → E) (C : Set E)
    (hC : IsCompact C) (hmem : ∀ ε : ℝ, 0 < ε → f ε ∈ C)
    (hmono : MonotoneOn f (Ioi (0 : ℝ))) :
    ∃ G₀ : E, G₀ ∈ C ∧ IsGLB (f '' Ioi (0 : ℝ)) G₀ ∧
      Tendsto f (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀) := by
  have hev : ∀ᶠ ε in nhdsWithin 0 (Ioi (0 : ℝ)), f ε ∈ C :=
    by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hmem ε hε
  obtain ⟨G₀, hG₀, hc⟩ := hC.exists_mapClusterPt (Filter.tendsto_principal.mpr hev)
  have hglb : ∀ y : E, MapClusterPt y (nhdsWithin 0 (Ioi (0 : ℝ))) f →
      IsGLB (f '' Ioi (0 : ℝ)) y := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rintro _ ⟨ε, hε, rfl⟩
      apply isClosed_Iic.mem_of_mapClusterPt hy
      filter_upwards [Ioo_mem_nhdsGT hε] with η hη
      exact hmono hη.1 hε hη.2.le
    · intro z hz
      apply isClosed_Ici.mem_of_mapClusterPt hy
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hz (mem_image_of_mem f hε)
  refine ⟨G₀, hG₀, hglb G₀ hc, ?_⟩
  apply hC.tendsto_nhds_of_unique_mapClusterPt hev
  intro y _ hy
  exact (hglb y hy).unique (hglb G₀ hc)
