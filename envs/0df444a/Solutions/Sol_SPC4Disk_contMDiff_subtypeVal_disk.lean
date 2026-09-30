-- Prove2me | solution 1 for SPC4Disk.contMDiff_subtypeVal_disk
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:02:21.604982+00:00
-- url     : https://prove2.me/submissions/f5cff91c-0417-4cf6-a61e-d99f1d51ea50

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_SPC4DiskCharts
import Theorems.Thm_SPC4Disk_diskIsManifold

attribute [local instance] SPC4Disk.diskIsManifold

set_option autoImplicit false

namespace SPC4Disk.SupplementAux_contMDiff_subtypeVal_disk

open Set Metric

open scoped ContDiff Manifold

noncomputable section

variable {n : ℕ} [NeZero n]

section BoundaryChart

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The chain from half-space coordinates to the sphere through the inverse
stereographic map is globally smooth (the shared core of the reverse and
boundary-to-boundary transitions). -/
lemma _root_.SPC4Disk.SupplementAux_contMDiff_subtypeVal_disk.contDiff_sphereLift
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        (((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p))).repr.symm
          (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
            EuclideanSpace ℝ (Fin (m + 1)))) := by
  have htail : ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (WithLp.toLp 2 (Fin.tail (fun j => y j)) : EuclideanSpace ℝ (Fin m))) := by
    refine PiLp.contDiff_toLp.comp (contDiff_pi.mpr fun j => ?_)
    exact ((ContinuousLinearMap.proj (j.succ : Fin (m + 1)) :
      ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp PiLp.contDiff_ofLp
  refine (contDiff_stereoInvFunAux (m := k)).comp ?_
  refine ((Submodule.subtypeL _ :
    _ →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).contDiff).comp ?_
  exact (((OrthonormalBasis.fromOrthogonalSpanSingleton m
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm.contDiff :
      ContDiff ℝ k _)).comp htail

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
end SPC4Disk.SupplementAux_contMDiff_subtypeVal_disk

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

open SPC4Disk in
theorem solution {k : ℕ∞ω} :
    ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) k
      (Subtype.val : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 →
        EuclideanSpace ℝ (Fin (m + 1))) := by
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, fun x y => ?_⟩
  simp only [mfld_simps, chartAt_self_eq]
  by_cases h : ‖x.val‖ < 1
  · have hchart : chartAt (EuclideanHalfSpace (m + 1)) x =
        if ‖x.val‖ < 1 then SPC4Disk.DiskInteriorChart
        else SPC4Disk.DiskBoundaryChart (SPC4Disk.unitOr SPC4Disk.diskNorth x.val) := rfl
    rw [hchart, if_pos h]
    refine ((contDiff_id.sub (contDiff_const (c := SPC4Disk.diskShift (m + 1)))).contDiffOn).congr ?_
    rintro v hv
    simp only [SPC4Disk.DiskInteriorChart, modelWithCornersEuclideanHalfSpace,
      mfld_simps] at hv ⊢
    obtain ⟨u, hu⟩ := hv.1
    have hv0 : (0 : ℝ) ≤ v.ofLp 0 := by rw [← hu]; exact u.2
    have hupd : WithLp.toLp 2 (Function.update v.ofLp 0 (max (v.ofLp 0) 0)) = v := by
      rw [max_eq_left hv0, Function.update_eq_self, WithLp.toLp_ofLp]
    rw [hupd] at hv ⊢
    exact SPC4Disk.radialClamp_of_le _ (le_of_lt hv.2)
  · have hchart : chartAt (EuclideanHalfSpace (m + 1)) x =
        if ‖x.val‖ < 1 then SPC4Disk.DiskInteriorChart
        else SPC4Disk.DiskBoundaryChart (SPC4Disk.unitOr SPC4Disk.diskNorth x.val) := rfl
    rw [hchart, if_neg h]
    have h0 : ContDiff ℝ k (fun v : EuclideanSpace ℝ (Fin (m + 1)) => 1 - v 0) := by
      refine contDiff_const.sub ?_
      exact ((ContinuousLinearMap.proj (0 : Fin (m + 1)) :
        ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp PiLp.contDiff_ofLp
    refine ((h0.smul (SPC4Disk.SupplementAux_contMDiff_subtypeVal_disk.contDiff_sphereLift (SPC4Disk.unitOr SPC4Disk.diskNorth x.val))).contDiffOn).congr ?_
    rintro v hv
    simp only [SPC4Disk.DiskBoundaryChart, SPC4Disk.DiskBoundaryChartInv,
      modelWithCornersEuclideanHalfSpace, mfld_simps] at hv ⊢
    obtain ⟨u', hu'⟩ := hv.1
    have hv0 : (0 : ℝ) ≤ v.ofLp 0 := by rw [← hu']; exact u'.2
    have hupd : WithLp.toLp 2 (Function.update v.ofLp 0 (max (v.ofLp 0) 0)) = v := by
      rw [max_eq_left hv0, Function.update_eq_self, WithLp.toLp_ofLp]
    simp only [Function.update_self, max_eq_left hv0] at hv
    have hv1 : v.ofLp 0 < 1 := hv.2
    simp only [hupd]
    show (0 ⊔ (1 ⊓ (1 - v.ofLp 0))) • _ = _
    rw [SPC4Disk.diskClamp_eq hv0 hv1.le]
    rfl
