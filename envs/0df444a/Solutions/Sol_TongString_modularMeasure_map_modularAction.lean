-- Prove2me | solution 1 for TongString.modularMeasure_map_modularAction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:30:28.677961+00:00
-- url     : https://prove2.me/submissions/1513d244-c465-44a9-a796-8e17b4172357

import Mathlib
import Definitions.Def_TongString_modular_action

set_option autoImplicit false

namespace TongString

open MeasureTheory

lemma modularMeasure_eq_map_coe :
    modularMeasure = Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane) := by
  ext s hs
  rw [Measure.map_apply UpperHalfPlane.measurable_coe hs, UpperHalfPlane.volume_eq_lintegral,
    modularMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]
  have himg : UpperHalfPlane.coe '' (UpperHalfPlane.coe ⁻¹' s) = s ∩ {τ : ℂ | 0 < τ.im} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, w.im_pos⟩
    · rintro ⟨hz, hz'⟩
      exact ⟨⟨z, hz'⟩, hz, rfl⟩
  rw [himg]
  refine setLIntegral_congr_fun (hs.inter (measurableSet_lt measurable_const Complex.measurable_im)) ?_
  intro z hz
  have hz2 : 0 < z.im := hz.2
  show ENNReal.ofReal (1 / z.im ^ 2) = ((((1 / ‖z.im‖₊) ^ 2 : NNReal)) : ENNReal)
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [Real.norm_eq_abs, abs_of_pos hz2]

lemma measurable_modularAction (a b c d : ℤ) : Measurable (modularAction a b c d) := by
  unfold modularAction
  fun_prop

theorem modularMeasure_map_modularAction_aux (a b c d : ℤ) (h : a * d - b * c = 1) :
    modularMeasure.map (modularAction a b c d) = modularMeasure := by
  have hdetR : ((a : ℝ) * d - b * c) = 1 := by exact_mod_cast h
  let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℝ), b; c, d]
    (by rw [Matrix.det_fin_two_of, hdetR]; exact one_ne_zero)
  have hdet : 0 < g.det.val := by
    simp [g, Matrix.det_fin_two_of, hdetR]
  have hcomp : modularAction a b c d ∘ UpperHalfPlane.coe =
      UpperHalfPlane.coe ∘ (fun τ : UpperHalfPlane => g • τ) := by
    funext τ
    simp only [Function.comp, UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num,
      UpperHalfPlane.denom, modularAction, g]
    simp
  have hmeas : Measurable (fun τ : UpperHalfPlane => g • τ) := by
    rw [← UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff, ← hcomp]
    exact (measurable_modularAction a b c d).comp UpperHalfPlane.measurable_coe
  rw [modularMeasure_eq_map_coe, Measure.map_map (measurable_modularAction a b c d)
    UpperHalfPlane.measurable_coe, hcomp, ← Measure.map_map UpperHalfPlane.measurable_coe hmeas,
    MeasureTheory.map_smul]

end TongString

open MeasureTheory in
open TongString in
theorem solution (a b c d : ℤ) (h : a * d - b * c = 1) :
    modularMeasure.map (modularAction a b c d) = modularMeasure := by
  exact TongString.modularMeasure_map_modularAction_aux a b c d h
