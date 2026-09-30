-- Prove2me | solution 1 for SPC4Disk.contMDiff_diskCollar
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:05:25.278805+00:00
-- url     : https://prove2.me/submissions/c6c8d172-c551-419b-953c-265b2bfcd1ba

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SPC4DiskCollar
import Theorems.Thm_SPC4Disk_contMDiff_iff_comp_subtypeVal_disk

set_option autoImplicit false

namespace SPC4Disk.SupplementAux_contMDiff_diskCollar

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

lemma _root_.SPC4Disk.SupplementAux_contMDiff_diskCollar.continuous_diskCollar : Continuous (SPC4Disk.diskCollar (m := m)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub ((continuous_subtype_val.comp
    continuous_snd).div_const 2)).smul
    (continuous_subtype_val.comp continuous_fst))

/-- The vector-level collar map is smooth on the product
manifold-with-boundary. -/
lemma _root_.SPC4Disk.SupplementAux_contMDiff_diskCollar.contMDiff_diskCollarVal :
    ContMDiff ((𝓡 m).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞
      (fun p : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ×
          (Set.Icc (0 : ℝ) 1) =>
        (1 - p.2.val / 2) • p.1.val) := by
  have ht : ContMDiff ((𝓡 m).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
      (fun p : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ×
          (Set.Icc (0 : ℝ) 1) => 1 - p.2.val / 2) := by
    have hval := (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)
      (n := (∞ : ℕ∞ω))).comp
      (contMDiff_snd (I := 𝓡 m) (M := sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))
    exact ((contDiff_const.sub (contDiff_id.div_const 2)).contMDiff).comp hval
  have hu : ContMDiff ((𝓡 m).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞
      (fun p : (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) ×
          (Set.Icc (0 : ℝ) 1) => p.1.val) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  exact ht.smul hu

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
end SPC4Disk.SupplementAux_contMDiff_diskCollar

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

open SPC4Disk in
theorem solution :
    ContMDiff ((𝓡 m).prod (𝓡∂ 1)) (𝓡∂ (m + 1)) ∞ (SPC4Disk.diskCollar (m := m)) :=
  SPC4Disk.contMDiff_iff_comp_subtypeVal_disk.mpr
    ⟨SPC4Disk.SupplementAux_contMDiff_diskCollar.continuous_diskCollar, SPC4Disk.SupplementAux_contMDiff_diskCollar.contMDiff_diskCollarVal⟩
