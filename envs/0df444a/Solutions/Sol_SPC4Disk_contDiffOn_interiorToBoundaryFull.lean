-- Prove2me | solution 1 for SPC4Disk.contDiffOn_interiorToBoundaryFull
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T05:58:58.248766+00:00
-- url     : https://prove2.me/submissions/37c5c2ac-d004-4dd9-a590-acc7bed1b98a

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

lemma contDiffOn_unitVector {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ‖x‖⁻¹ • x)
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 } := by
  intro x hx
  have h1 : ContDiffAt ℝ k (norm : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) x :=
    contDiffAt_norm (𝕜 := ℝ) hx
  exact ((h1.inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id).contDiffWithinAt

lemma contDiffOn_boundaryAngular
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p))).repr
          (stereoToFun (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) (‖x‖⁻¹ • x))))
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (‖x‖⁻¹ • x) ≠ (1 : ℝ) } := by
  refine ContDiff.comp_contDiffOn
    ((OrthonormalBasis.fromOrthogonalSpanSingleton m
      (ne_zero_of_mem_unit_sphere (-p))).repr.contDiff :
      ContDiff ℝ k _) ?_
  refine ContDiffOn.comp contDiffOn_stereoToFun
    (contDiffOn_unitVector.mono fun x hx => hx.1) ?_
  exact fun x hx => hx.2

/-- The radial coordinate `1 - ‖x‖` is smooth away from the origin. -/
lemma contDiffOn_oneSubNorm {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun x : EuclideanSpace ℝ (Fin (m + 1)) => 1 - ‖x‖)
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 } :=
  fun _ hx => (contDiffAt_const.sub (contDiffAt_norm (𝕜 := ℝ) hx)).contDiffWithinAt

end SPC4Disk

open SPC4Disk in
theorem solution
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
        (WithLp.toLp 2 (Fin.cons (1 - ‖v - diskShift (m + 1)‖)
          (fun i => ((OrthonormalBasis.fromOrthogonalSpanSingleton m
              (ne_zero_of_mem_unit_sphere (-p))).repr
            (stereoToFun (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (‖v - diskShift (m + 1)‖⁻¹ • (v - diskShift (m + 1))))) i)) :
          EuclideanSpace ℝ (Fin (m + 1))))
      { v : EuclideanSpace ℝ (Fin (m + 1)) | v - diskShift (m + 1) ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
          (‖v - diskShift (m + 1)‖⁻¹ • (v - diskShift (m + 1))) ≠ (1 : ℝ) } := by
  have hshift : ContDiff ℝ k (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      v - diskShift (m + 1)) := contDiff_id.sub contDiff_const
  have hmapsto : Set.MapsTo (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
      v - diskShift (m + 1))
      { v : EuclideanSpace ℝ (Fin (m + 1)) | v - diskShift (m + 1) ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
          (‖v - diskShift (m + 1)‖⁻¹ • (v - diskShift (m + 1))) ≠ (1 : ℝ) }
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (‖x‖⁻¹ • x) ≠ (1 : ℝ) } :=
    fun v hv => hv
  refine ContDiff.comp_contDiffOn PiLp.contDiff_toLp ?_
  refine contDiffOn_pi.mpr fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact (contDiffOn_oneSubNorm.comp hshift.contDiffOn fun v hv => hv.1)
  · simp only [Fin.cons_succ]
    exact ContDiff.comp_contDiffOn
      (((ContinuousLinearMap.proj (i : Fin m) :
        ((Fin m) → ℝ) →L[ℝ] ℝ).contDiff).comp (PiLp.contDiff_ofLp (𝕜 := ℝ)))
      ((contDiffOn_boundaryAngular p).comp hshift.contDiffOn hmapsto)
