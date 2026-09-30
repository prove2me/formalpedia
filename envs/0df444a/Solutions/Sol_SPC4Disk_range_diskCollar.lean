-- Prove2me | solution 1 for SPC4Disk.range_diskCollar
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T05:59:12.92118+00:00
-- url     : https://prove2.me/submissions/55e0ba5c-c7b6-4874-a61d-98e54d9fc000

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SPC4DiskCollar

set_option autoImplicit false

namespace SPC4Disk.SupplementAux_range_diskCollar

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
end SPC4Disk.SupplementAux_range_diskCollar

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

open SPC4Disk in
theorem solution :
    Set.range (SPC4Disk.diskCollar (m := m)) =
      { z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        1 / 2 ≤ ‖z.val‖ } := by
  ext z
  constructor
  · rintro ⟨⟨u, t⟩, rfl⟩
    have hnu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have hpt : (0 : ℝ) ≤ 1 - t.val / 2 := by linarith [t.2.2]
    show 1 / 2 ≤ ‖(1 - t.val / 2) • u.val‖
    rw [norm_smul, hnu, mul_one, Real.norm_eq_abs, abs_of_nonneg hpt]
    linarith [t.2.2]
  · intro hz
    have hz' : (1 : ℝ) / 2 ≤ ‖z.val‖ := hz
    have hz1 : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
    have hzne : z.val ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz'
      linarith
    refine ⟨⟨SPC4Disk.unitOr SPC4Disk.diskNorth z.val,
      ⟨2 * (1 - ‖z.val‖), ⟨by linarith, by linarith [hz']⟩⟩⟩, ?_⟩
    apply Subtype.ext
    show (1 - (2 * (1 - ‖z.val‖)) / 2) • (SPC4Disk.unitOr SPC4Disk.diskNorth z.val).val = z.val
    have hr : 1 - (2 * (1 - ‖z.val‖)) / 2 = ‖z.val‖ := by ring
    rw [hr, SPC4Disk.smul_unitOr SPC4Disk.diskNorth hzne]
