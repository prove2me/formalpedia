-- Prove2me | solution 1 for RoughSurfaceScattering.h1Norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:09:46.179138+00:00
-- url     : https://prove2.me/submissions/a697f8ad-3f49-449c-a5ec-853dff84538d

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory
open RoughSurfaceScattering

/-- The `ℂ³`-valued map `x ↦ (u x, ∂₁u x, ∂₂u x)`, whose `L²(D)` norm is `‖u‖_{H¹(D)}`. -/
noncomputable def jet (u : R2 → ℂ) (x : R2) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 ![u x, fderiv ℝ u x (EuclideanSpace.single 0 1),
    fderiv ℝ u x (EuclideanSpace.single 1 1)]

lemma enorm_jet_sq (u : R2 → ℂ) (x : R2) :
    ‖jet u x‖ₑ ^ (2 : ℝ) = ‖u x‖ₑ ^ 2 + ‖fderiv ℝ u x (EuclideanSpace.single 0 1)‖ₑ ^ 2 +
      ‖fderiv ℝ u x (EuclideanSpace.single 1 1)‖ₑ ^ 2 := by
  rw [ENNReal.rpow_two, ← ofReal_norm (jet u x), ← ENNReal.ofReal_pow (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [jet, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma h1Norm_eq_eLpNorm_jet (D : Set R2) (u : R2 → ℂ) :
    h1Norm D u = eLpNorm (jet u) 2 (volume.restrict D) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, enorm_jet_sq]
  rfl

lemma continuousOn_jet (D : Set R2) (hD : IsOpen D) (u : R2 → ℂ) (hu : ContDiffOn ℝ 1 u D) :
    ContinuousOn (jet u) D := by
  have hfd := hu.continuousOn_fderiv_of_isOpen hD le_rfl
  have h0 : ContinuousOn (fun x => fderiv ℝ u x (EuclideanSpace.single 0 1)) D :=
    (continuous_id.clm_apply continuous_const).comp_continuousOn hfd
  have h1 : ContinuousOn (fun x => fderiv ℝ u x (EuclideanSpace.single 1 1)) D :=
    (continuous_id.clm_apply continuous_const).comp_continuousOn hfd
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn ?_
  refine continuousOn_pi.mpr fun i => ?_
  fin_cases i
  · exact hu.continuousOn
  · exact h0
  · exact h1

theorem solution (D : Set R2) (hD : IsOpen D) (v w : R2 → ℂ)
    (hv : ContDiffOn ℝ 1 v D) (hw : ContDiffOn ℝ 1 w D) :
    h1Norm D (fun x => v x - w x) ≤ h1Norm D v + h1Norm D w := by
  have hDm : MeasurableSet D := hD.measurableSet
  have hjet : jet (fun x => v x - w x) =ᵐ[volume.restrict D] jet v - jet w := by
    filter_upwards [ae_restrict_mem hDm] with x hx
    have hvx : DifferentiableAt ℝ v x :=
      (hv.differentiableOn one_ne_zero x hx).differentiableAt (hD.mem_nhds hx)
    have hwx : DifferentiableAt ℝ w x :=
      (hw.differentiableOn one_ne_zero x hx).differentiableAt (hD.mem_nhds hx)
    have hd : fderiv ℝ (fun x => v x - w x) x = fderiv ℝ v x - fderiv ℝ w x :=
      fderiv_sub hvx hwx
    ext i
    fin_cases i <;> simp [jet, hd]
  rw [h1Norm_eq_eLpNorm_jet, h1Norm_eq_eLpNorm_jet, h1Norm_eq_eLpNorm_jet, eLpNorm_congr_ae hjet]
  exact eLpNorm_sub_le ((continuousOn_jet D hD v hv).aestronglyMeasurable hDm)
    ((continuousOn_jet D hD w hw).aestronglyMeasurable hDm) (by norm_num)
