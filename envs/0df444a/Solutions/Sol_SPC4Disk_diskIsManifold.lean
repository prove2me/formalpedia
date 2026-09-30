-- Prove2me | solution 1 for SPC4Disk.diskIsManifold
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:00:25.462607+00:00
-- url     : https://prove2.me/submissions/2c2246ec-6216-4d9e-be87-0dc55ced5992

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Theorems.Thm_SPC4Disk_contDiffOn_boundaryToBoundary
import Theorems.Thm_SPC4Disk_contDiffOn_interiorToBoundaryFull
import Theorems.Thm_SPC4Disk_contDiff_boundaryInv

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace SPC4Disk

/-- Off the `-p` ray, the unit vector's inner product with `-p` avoids `1` —
the bridge from the chart's source condition to `stereoToFun`'s smoothness
domain (equality case of Cauchy–Schwarz). -/
lemma inner_unit_ne_one (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ≠ 0) (hp : unitOr p x ≠ -p) :
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
  rw [unitOr_val_of_ne p hx, ← hu, ← h3]

end SPC4Disk

open SPC4Disk in
set_option maxHeartbeats 800000 in
theorem solution {k : ℕ∞ω} :
    IsManifold (𝓡∂ (m + 1)) k
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [atlas] at he he'
  rcases he with (rfl | ⟨p, rfl⟩) <;> rcases he' with (rfl | ⟨p', rfl⟩)
  · exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1
  · refine ((contDiffOn_interiorToBoundaryFull p').mono ?_).congr ?_
    · rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
      simp only [OpenPartialHomeomorph.symm_symm, DiskInteriorChart,
        DiskBoundaryChart, modelWithCornersEuclideanHalfSpace,
        mfld_simps] at hz₁ hz₂
      have hupd : WithLp.toLp 2 (Function.update z.ofLp 0 (max (z.ofLp 0) 0)) = z := by
        rw [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp]
      rw [hupd] at hz₁ hz₂
      rw [radialClamp_of_le _ hz₁.le] at hz₂
      exact ⟨hz₂.1, inner_unit_ne_one p' hz₂.1 (unitOr_ne_neg p' hz₂.1 hz₂.2)⟩
    · rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
      simp only [OpenPartialHomeomorph.symm_symm, DiskInteriorChart,
        DiskBoundaryChart, modelWithCornersEuclideanHalfSpace,
        mfld_simps] at hz₁ hz₂
      have hupd : WithLp.toLp 2 (Function.update z.ofLp 0 (max (z.ofLp 0) 0)) = z := by
        rw [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp]
      rw [hupd] at hz₁ hz₂
      have hne : z - diskShift (m + 1) ≠ 0 := by
        have := hz₂.1
        rwa [radialClamp_of_le _ hz₁.le] at this
      simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply,
        ModelWithCorners.left_inv, DiskInteriorChart, DiskBoundaryChart,
        modelWithCornersEuclideanHalfSpace, mfld_simps]
      simp only [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp]
      have harg : (⟨radialClamp (z - diskShift (m + 1)),
          mem_closedBall_zero_iff.mpr (norm_radialClamp_le _)⟩ :
            closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) =
          ⟨z - diskShift (m + 1), mem_closedBall_zero_iff.mpr hz₁.le⟩ :=
        Subtype.ext (radialClamp_of_le _ hz₁.le)
      rw [harg]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [DiskBoundaryChartFun]
      · simp [DiskBoundaryChartFun, unitOr_val_of_ne p' hne,
          stereographic', stereographic, stereoToFun, mfld_simps,
          map_sub, real_inner_smul_right, smul_smul, -coe_neg_sphere]
  · apply (contDiff_boundaryInv p).contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
    simp only [OpenPartialHomeomorph.symm_symm, ModelWithCorners.left_inv,
      DiskInteriorChart, DiskBoundaryChart, modelWithCornersEuclideanHalfSpace,
      mfld_simps] at hz₁ hz₂
    simp only [Function.update_self, max_eq_left hz₀] at hz₁
    simp only [Function.comp_apply, ModelWithCorners.left_inv, DiskInteriorChart,
      DiskBoundaryChart, DiskBoundaryChartInv, modelWithCornersEuclideanHalfSpace,
      stereographic', stereographic, stereoInvFun, mfld_simps]
    simp only [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp,
      diskClamp_eq hz₀ hz₁.le]
    show (DiskBoundaryChartInv p ⟨z, hz₀⟩ : EuclideanSpace ℝ (Fin (m + 1))) +
      diskShift (m + 1) = _
    simp only [DiskBoundaryChartInv, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      stereographic', stereographic, stereoInvFun, mfld_simps]
    simp only [diskClamp_eq hz₀ hz₁.le]
    rfl
  · refine ((contDiffOn_boundaryToBoundary p p').mono ?_).congr ?_
    · rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
      simp only [OpenPartialHomeomorph.symm_symm, DiskBoundaryChart,
        modelWithCornersEuclideanHalfSpace, mfld_simps] at hz₁ hz₂
      simp only [Function.update_self, max_eq_left hz₀] at hz₁
      have hupd : WithLp.toLp 2 (Function.update z.ofLp 0 (max (z.ofLp 0) 0)) = z := by
        rw [max_eq_left hz₀, Function.update_eq_self, WithLp.toLp_ofLp]
      simp only [hupd] at hz₂
      have hr : 0 < 1 - z.ofLp 0 := by linarith
      set u := (stereographic' m (-p)).symm
        (WithLp.toLp 2 (Fin.tail (fun i => z.ofLp i))) with hu
      have h22 : (0 ⊔ (1 ⊓ (1 - z.ofLp 0))) • (u : EuclideanSpace ℝ (Fin (m + 1))) ≠
          ‖(0 ⊔ (1 ⊓ (1 - z.ofLp 0))) • (u : EuclideanSpace ℝ (Fin (m + 1)))‖ •
            ((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1))) := hz₂.2
      rw [diskClamp_eq hz₀ hz₁.le] at h22
      have huval : ‖(u : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp u.2
      have hnorm : ‖(1 - z.ofLp 0) • (u : EuclideanSpace ℝ (Fin (m + 1)))‖ =
          1 - z.ofLp 0 := by
        rw [norm_smul, huval, mul_one, Real.norm_eq_abs, abs_of_pos hr]
      rw [hnorm] at h22
      have hne' : (u : EuclideanSpace ℝ (Fin (m + 1))) ≠
          ((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) := by
        intro h
        apply h22
        conv_lhs => rw [h]
      intro h1
      have hq : ‖((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp (-p').2
      have h2 : (inner ℝ ((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1))) (u : EuclideanSpace ℝ (Fin (m + 1))) : ℝ) =
          ‖((-p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))‖ * ‖(u : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
        rw [hq, huval, one_mul]
        exact h1
      have h3 := inner_eq_norm_mul_iff.mp h2
      rw [hq, huval] at h3
      simp only [RCLike.ofReal_one, one_smul] at h3
      exact hne' h3.symm
    · rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
      simp only [OpenPartialHomeomorph.symm_symm, DiskBoundaryChart,
        modelWithCornersEuclideanHalfSpace, mfld_simps] at hz₁ hz₂
      simp only [Function.update_self, max_eq_left hz₀] at hz₁
      have hr : 0 < 1 - z.ofLp 0 := by linarith
      set u := (stereographic' m (-p)).symm
        (WithLp.toLp 2 (Fin.tail (fun i => z.ofLp i))) with hu
      have huval : ‖(u : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp u.2
      have hnorm : ‖(1 - z.ofLp 0) • (u : EuclideanSpace ℝ (Fin (m + 1)))‖ =
          1 - z.ofLp 0 := by
        rw [norm_smul, huval, mul_one, Real.norm_eq_abs, abs_of_pos hr]
      rw [Function.comp_apply, Function.comp_apply, ModelWithCorners.left_inv,
        OpenPartialHomeomorph.trans_apply]
      show (DiskBoundaryChartFun p' (DiskBoundaryChartInv p ⟨z, hz₀⟩)).val = _
      have hIv : ((DiskBoundaryChartInv p ⟨z, hz₀⟩) :
          EuclideanSpace ℝ (Fin (m + 1))) =
          (0 ⊔ (1 ⊓ (1 - z.ofLp 0))) • (u : EuclideanSpace ℝ (Fin (m + 1))) := rfl
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [DiskBoundaryChartFun_val_zero, hIv, diskClamp_eq hz₀ hz₁.le,
          hnorm, sub_sub_cancel, Fin.cons_zero, WithLp.ofLp_toLp,
          modelWithCornersEuclideanHalfSpace, mfld_simps]
      · simp only [DiskBoundaryChartFun_val_succ, hIv, diskClamp_eq hz₀ hz₁.le,
          unitOr_smul p' hr, stereographic', stereographic, Fin.cons_succ,
          WithLp.ofLp_toLp, modelWithCornersEuclideanHalfSpace, mfld_simps]
        rfl
