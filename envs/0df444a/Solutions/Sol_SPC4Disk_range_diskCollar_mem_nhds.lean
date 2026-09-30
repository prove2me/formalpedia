-- Prove2me | solution 1 for SPC4Disk.range_diskCollar_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:00:10.445532+00:00
-- url     : https://prove2.me/submissions/517e385a-e94c-4bc5-b8fc-72199d28e618

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SPC4DiskCollar
import Theorems.Thm_SPC4Disk_diskBoundary_eq
import Theorems.Thm_SPC4Disk_range_diskCollar

set_option autoImplicit false

namespace SPC4Disk.SupplementAux_range_diskCollar_mem_nhds

open Set Metric

open scoped ContDiff Manifold

noncomputable section

variable {n : ℕ} [NeZero n]

section BoundaryChart

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end BoundaryChart

section BoundarySmooth

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end BoundarySmooth

section Collar

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end Collar

section ValSmooth

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

end ValSmooth

section Annulus

variable {m : ℕ}

end Annulus

end
end SPC4Disk.SupplementAux_range_diskCollar_mem_nhds

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

open SPC4Disk in
theorem solution
    {z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hz : z ∈ (𝓡∂ (m + 1)).boundary
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) :
    Set.range (SPC4Disk.diskCollar (m := m)) ∈ nhds z := by
  rw [SPC4Disk.diskBoundary_eq] at hz
  have hopen : IsOpen { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      1 / 2 < ‖w.val‖ } := by
    have h : IsOpen { v : EuclideanSpace ℝ (Fin (m + 1)) | 1 / 2 < ‖v‖ } :=
      isOpen_lt continuous_const continuous_norm
    exact h.preimage continuous_subtype_val
  have hmem : z ∈ { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      1 / 2 < ‖w.val‖ } := by
    show (1 : ℝ) / 2 < ‖z.val‖
    rw [hz]
    norm_num
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  rw [SPC4Disk.range_diskCollar]
  intro w hw
  show (1 : ℝ) / 2 ≤ ‖w.val‖
  exact le_of_lt hw
