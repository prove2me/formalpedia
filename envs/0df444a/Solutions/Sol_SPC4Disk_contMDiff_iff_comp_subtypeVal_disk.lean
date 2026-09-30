-- Prove2me | solution 1 for SPC4Disk.contMDiff_iff_comp_subtypeVal_disk
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:04:01.705961+00:00
-- url     : https://prove2.me/submissions/033dfe03-dcf6-41c4-9af3-04fe202315ad

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_SPC4DiskCharts
import Theorems.Thm_SPC4Disk_contMDiff_subtypeVal_disk
import Theorems.Thm_SPC4Disk_diskIsManifold

attribute [local instance] SPC4Disk.diskIsManifold

set_option autoImplicit false

namespace SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk

open Set Metric

open scoped ContDiff Manifold

noncomputable section

variable {n : ℕ} [NeZero n]

section BoundaryChart

variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

lemma _root_.SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.contDiffOn_unitVector {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ‖x‖⁻¹ • x)
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 } := by
  intro x hx
  have h1 : ContDiffAt ℝ k (norm : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) x :=
    contDiffAt_norm (𝕜 := ℝ) hx
  exact ((h1.inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id).contDiffWithinAt

lemma _root_.SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.contDiffOn_boundaryAngular
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
    (SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.contDiffOn_unitVector.mono fun x hx => hx.1) ?_
  exact fun x hx => hx.2

/-- Off the `-p` ray, the unit vector's inner product with `-p` avoids `1` —
the bridge from the chart's source condition to `stereoToFun`'s smoothness
domain (equality case of Cauchy–Schwarz). -/
lemma _root_.SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.inner_unit_ne_one (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ≠ 0) (hp : SPC4Disk.unitOr p x ≠ -p) :
    innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1))) (‖x‖⁻¹ • x) ≠ (1 : ℝ) := by
  set q : EuclideanSpace ℝ (Fin (m + 1)) :=
    (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
      EuclideanSpace ℝ (Fin (m + 1))) with hqdef
  set u : EuclideanSpace ℝ (Fin (m + 1)) := ‖x‖⁻¹ • x with hu
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hq : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp (-p).2
  intro h1
  have h2 : (inner ℝ q u : ℝ) = ‖q‖ * ‖u‖ := by
    rw [hq, hnu, one_mul]
    exact h1
  have h3 := inner_eq_norm_mul_iff.mp h2
  rw [hq, hnu] at h3
  simp only [RCLike.ofReal_one, one_smul] at h3
  apply hp
  ext1
  rw [SPC4Disk.unitOr_val_of_ne p hx, ← hu, ← h3]

/-- The radial coordinate `1 - ‖x‖` is smooth away from the origin. -/
lemma _root_.SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.contDiffOn_oneSubNorm {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun x : EuclideanSpace ℝ (Fin (m + 1)) => 1 - ‖x‖)
      { x : EuclideanSpace ℝ (Fin (m + 1)) | x ≠ 0 } :=
  fun _ hx => (contDiffAt_const.sub (contDiffAt_norm (𝕜 := ℝ) hx)).contDiffWithinAt

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

/-- Forward half of the into-disk characterization: postcomposing with the
smooth inclusion preserves smoothness. -/
lemma _root_.ContMDiff.subtypeVal_disk_comp_sp4Export_contMDiff_iff_comp_subtypeVal_disk {k : ℕ∞ω}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    {f : M → closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hf : ContMDiff I (𝓡∂ (m + 1)) k f) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) k
      (fun a => (f a).val) :=
  SPC4Disk.contMDiff_subtypeVal_disk.comp hf

/-- The pure boundary-chart-forward formula (no shift) is smooth on the good
set — the last analytic ingredient for the reverse direction of the
into-disk characterization. -/
lemma _root_.SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.contDiffOn_boundaryChartFunVal
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
        (WithLp.toLp 2 (Fin.cons (1 - ‖v‖)
          (fun i => ((OrthonormalBasis.fromOrthogonalSpanSingleton m
              (ne_zero_of_mem_unit_sphere (-p))).repr
            (stereoToFun (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (‖v‖⁻¹ • v))) i)) :
          EuclideanSpace ℝ (Fin (m + 1))))
      { v : EuclideanSpace ℝ (Fin (m + 1)) | v ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (‖v‖⁻¹ • v) ≠ (1 : ℝ) } := by
  refine ContDiff.comp_contDiffOn PiLp.contDiff_toLp ?_
  refine contDiffOn_pi.mpr fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.contDiffOn_oneSubNorm.mono fun v hv => hv.1
  · simp only [Fin.cons_succ]
    exact ContDiff.comp_contDiffOn
      (((ContinuousLinearMap.proj (i : Fin m) :
        ((Fin m) → ℝ) →L[ℝ] ℝ).contDiff).comp (PiLp.contDiff_ofLp (𝕜 := ℝ)))
      (SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.contDiffOn_boundaryAngular p)

end ValSmooth

section Annulus

variable {m : ℕ}

end Annulus

end
end SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

open SPC4Disk in
theorem solution {k : ℕ∞ω}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I k M]
    {f : M → closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1} :
    ContMDiff I (𝓡∂ (m + 1)) k f ↔
      Continuous f ∧
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) k
          (fun a => (f a).val) := by
  constructor
  · exact fun hf => ⟨hf.continuous, hf.subtypeVal_disk_comp_sp4Export_contMDiff_iff_comp_subtypeVal_disk⟩
  · rintro ⟨hc, hval⟩
    rw [contMDiff_iff]
    refine ⟨hc, fun x y => ?_⟩
    have hv2 := (contMDiff_iff.mp hval).2 x (0 : EuclideanSpace ℝ (Fin (m + 1)))
    simp only [mfld_simps, chartAt_self_eq] at hv2 ⊢
    by_cases h : ‖y.val‖ < 1
    · have hchart : chartAt (EuclideanHalfSpace (m + 1)) y =
          if ‖y.val‖ < 1 then SPC4Disk.DiskInteriorChart
          else SPC4Disk.DiskBoundaryChart (SPC4Disk.unitOr SPC4Disk.diskNorth y.val) := rfl
      rw [hchart, if_pos h]
      exact ((contDiff_id.add (contDiff_const (c := SPC4Disk.diskShift (m + 1)))).comp_contDiffOn
        (hv2.mono Set.inter_subset_left))
    · have hchart : chartAt (EuclideanHalfSpace (m + 1)) y =
          if ‖y.val‖ < 1 then SPC4Disk.DiskInteriorChart
          else SPC4Disk.DiskBoundaryChart (SPC4Disk.unitOr SPC4Disk.diskNorth y.val) := rfl
      rw [hchart, if_neg h]
      refine ContDiffOn.congr
        (ContDiffOn.comp (SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.contDiffOn_boundaryChartFunVal (SPC4Disk.unitOr SPC4Disk.diskNorth y.val))
          (hv2.mono Set.inter_subset_left) ?_) ?_
      · rintro v ⟨-, hv3⟩
        have hsrc := hv3
        simp only [SPC4Disk.DiskBoundaryChart, Set.mem_preimage, Function.comp_apply,
          mfld_simps] at hsrc
        exact ⟨hsrc.1, SPC4Disk.SupplementAux_contMDiff_iff_comp_subtypeVal_disk.inner_unit_ne_one _ hsrc.1
          (SPC4Disk.unitOr_ne_neg _ hsrc.1 hsrc.2)⟩
      · rintro v ⟨-, hv3⟩
        have hsrc := hv3
        simp only [SPC4Disk.DiskBoundaryChart, Set.mem_preimage, Function.comp_apply,
          mfld_simps] at hsrc
        show (SPC4Disk.DiskBoundaryChartFun (SPC4Disk.unitOr SPC4Disk.diskNorth y.val)
          (f ((chartAt H' x).symm (I.symm v)))).val = _
        simp only [SPC4Disk.DiskBoundaryChartFun, stereographic', stereographic,
          SPC4Disk.unitOr_val_of_ne _ hsrc.1, mfld_simps]
        rfl
