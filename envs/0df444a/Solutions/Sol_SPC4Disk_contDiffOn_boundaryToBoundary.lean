-- Prove2me | solution 1 for SPC4Disk.contDiffOn_boundaryToBoundary
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T05:57:39.963389+00:00
-- url     : https://prove2.me/submissions/f552ec5e-a9b7-4998-a17b-ff5c6854166b

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace SPC4Disk

/-- The chain from half-space coordinates to the sphere through the inverse
stereographic map is globally smooth (the shared core of the reverse and
boundary-to-boundary transitions). -/
lemma contDiff_sphereLift
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

end SPC4Disk

open SPC4Disk in
theorem solution
    (p p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        (WithLp.toLp 2 (Fin.cons (y 0)
          (fun i => ((OrthonormalBasis.fromOrthogonalSpanSingleton m
              (ne_zero_of_mem_unit_sphere (-p'))).repr
            (stereoToFun (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                  EuclideanSpace ℝ (Fin (m + 1)))
                (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
                  (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                    EuclideanSpace ℝ (Fin (m + 1)))))) i)) :
          EuclideanSpace ℝ (Fin (m + 1))))
      { y : EuclideanSpace ℝ (Fin (m + 1)) |
        innerSL ℝ (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1)))
            (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                (ne_zero_of_mem_unit_sphere (-p))).repr.symm
              (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                EuclideanSpace ℝ (Fin (m + 1)))) ≠ (1 : ℝ) } := by
  have hang : ContDiffOn ℝ k
      (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p'))).repr
          (stereoToFun (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1)))
            (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                  (ne_zero_of_mem_unit_sphere (-p))).repr.symm
                (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                  EuclideanSpace ℝ (Fin (m + 1)))))))
      { y : EuclideanSpace ℝ (Fin (m + 1)) |
        innerSL ℝ (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1)))
            (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                (ne_zero_of_mem_unit_sphere (-p))).repr.symm
              (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                EuclideanSpace ℝ (Fin (m + 1)))) ≠ (1 : ℝ) } := by
    refine ContDiff.comp_contDiffOn
      (((OrthonormalBasis.fromOrthogonalSpanSingleton m
        (ne_zero_of_mem_unit_sphere (-p'))).repr.contDiff : ContDiff ℝ k _)) ?_
    exact ContDiffOn.comp contDiffOn_stereoToFun
      (contDiff_sphereLift p).contDiffOn (fun y hy => hy)
  refine ContDiff.comp_contDiffOn PiLp.contDiff_toLp ?_
  refine contDiffOn_pi.mpr fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact (((ContinuousLinearMap.proj (0 : Fin (m + 1)) :
      ((Fin (m + 1)) → ℝ) →L[ℝ] ℝ).contDiff).comp
        (PiLp.contDiff_ofLp (𝕜 := ℝ))).contDiffOn
  · simp only [Fin.cons_succ]
    exact ContDiff.comp_contDiffOn
      (((ContinuousLinearMap.proj (i : Fin m) :
        ((Fin m) → ℝ) →L[ℝ] ℝ).contDiff).comp (PiLp.contDiff_ofLp (𝕜 := ℝ)))
      hang
