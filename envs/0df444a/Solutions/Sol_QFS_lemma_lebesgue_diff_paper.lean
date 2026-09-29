-- Prove2me | solution 1 for QFS.lemma_lebesgue_diff_paper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-06T18:44:20.664408+00:00
-- url     : https://prove2.me/submissions/c42ca2c3-a395-468a-b65f-9f5d5a0c939c

import Theorems.Thm_QFS_lemma_lebesgue_diff
import Theorems.Thm_QFS_cube_subset_closedCube
import Theorems.Thm_QFS_halfClosedCube_subset_closedCube
import Theorems.Thm_QFS_volume_cube
import Theorems.Thm_QFS_volume_closedCube
import Theorems.Thm_QFS_measurableSet_cube
import Definitions.Def_QFS_Section3
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric MeasureTheory ENNReal Filter Topology

variable {d : ℕ}

/-- The open and closed cubes agree up to a null set. -/
lemma QFS.cube_ae_eq_closedCube {h : ℝ} (hh : 0 < h) (u : EuclideanSpace ℝ (Fin d)) :
    QFS.cube h u =ᵐ[volume] QFS.closedCube h u := by
  have hsub := QFS.cube_subset_closedCube h u
  have hv : volume (QFS.closedCube h u) = volume (QFS.cube h u) := by
    rw [QFS.volume_closedCube hh.le, QFS.volume_cube hh]
  have hfin : volume (QFS.cube h u) ≠ ⊤ := by
    rw [QFS.volume_cube hh]; exact ENNReal.ofReal_ne_top
  refine (ae_eq_set).mpr ⟨?_, ?_⟩
  · simp [Set.sdiff_eq_empty.mpr hsub]
  · have := measure_sdiff hsub (QFS.measurableSet_cube hh u).nullMeasurableSet hfin
    rw [this, hv, tsub_self]

/-- **Lemma A.2 exactly as the source states it.** The hypothesis is membership in the
*half-closed* cube, the average is over the *open* cube, and the centres are lattice
points of `hℤ^d`.  Derived from `QFS.lemma_lebesgue_diff`, which assumes only membership
in the closed cube and is therefore strictly stronger. -/
theorem solution {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : LocallyIntegrable φ volume) :
    ∀ᵐ s : EuclideanSpace ℝ (Fin d),
      ∀ x : ℝ → EuclideanSpace ℝ (Fin d),
        (∀ h : ℝ, 0 < h → x h ∈ QFS.scaledLattice d h) →
        (∀ h : ℝ, 0 < h → s ∈ QFS.halfClosedCube h (x h)) →
        Tendsto (fun h => ⨍ y in QFS.cube h (x h), φ y) (𝓝[>] (0:ℝ)) (𝓝 (φ s)) := by
  filter_upwards [QFS.lemma_lebesgue_diff hφ] with s hs x _hlat hmem
  -- the averages over the open and closed cubes agree
  have hcong : ∀ h : ℝ, 0 < h →
      (⨍ y in QFS.cube h (x h), φ y) = ⨍ y in QFS.closedCube h (x h), φ y := by
    intro h hh
    exact setAverage_congr (QFS.cube_ae_eq_closedCube hh (x h))
  -- transport along the subtype of positive reals
  have hmapc : Filter.map (Subtype.val : ↥(Set.Ioi (0:ℝ)) → ℝ)
      (Filter.comap Subtype.val (𝓝[>] (0:ℝ))) = 𝓝[>] (0:ℝ) := by
    refine Filter.map_comap_of_mem ?_
    simpa [Subtype.range_coe, Set.Ioi] using self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0)
  have key := hs (ι := ↥(Set.Ioi (0:ℝ))) (l := Filter.comap Subtype.val (𝓝[>] (0:ℝ)))
      (fun i => (i : ℝ)) (fun i => x (i : ℝ))
      (fun i => i.2) (Filter.tendsto_comap.mono_right nhdsWithin_le_nhds)
      (fun i => QFS.halfClosedCube_subset_closedCube i.2.le (x (i:ℝ)) (hmem (i:ℝ) i.2))
  rw [← hmapc, Filter.tendsto_map'_iff]
  refine key.congr fun i => ?_
  exact (hcong (i : ℝ) i.2).symm
