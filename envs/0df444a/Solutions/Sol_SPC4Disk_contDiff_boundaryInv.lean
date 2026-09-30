-- Prove2me | solution 1 for SPC4Disk.contDiff_boundaryInv
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T05:57:38.923274+00:00
-- url     : https://prove2.me/submissions/8e3b8a45-e474-4fb0-b9a9-cf6d3e39cdf4

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

open SPC4Disk in
theorem solution
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (1 - y 0) • stereoInvFunAux
        (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        (((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p))).repr.symm
          (WithLp.toLp 2 (Fin.tail (fun i => y i)))) :
            EuclideanSpace ℝ (Fin (m + 1))) + diskShift (m + 1)) := by
  have h0 : ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) => 1 - y 0) := by
    refine contDiff_const.sub ?_
    exact ((ContinuousLinearMap.proj (0 : Fin (m + 1)) :
      ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp PiLp.contDiff_ofLp
  have htail : ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (WithLp.toLp 2 (Fin.tail (fun i => y i)) : EuclideanSpace ℝ (Fin m))) := by
    refine PiLp.contDiff_toLp.comp (contDiff_pi.mpr fun j => ?_)
    exact ((ContinuousLinearMap.proj (j.succ : Fin (m + 1)) :
      ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp PiLp.contDiff_ofLp
  have hrepr : ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (((OrthonormalBasis.fromOrthogonalSpanSingleton m
          (ne_zero_of_mem_unit_sphere (-p))).repr.symm
        (WithLp.toLp 2 (Fin.tail (fun i => y i)))) :
          EuclideanSpace ℝ (Fin (m + 1)))) := by
    refine ((Submodule.subtypeL _ :
      _ →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).contDiff).comp ?_
    exact (((OrthonormalBasis.fromOrthogonalSpanSingleton m
      (ne_zero_of_mem_unit_sphere (-p))).repr.symm.contDiff :
        ContDiff ℝ k _)).comp htail
  exact ((h0.smul ((contDiff_stereoInvFunAux (m := k)).comp hrepr)).add
    contDiff_const)
