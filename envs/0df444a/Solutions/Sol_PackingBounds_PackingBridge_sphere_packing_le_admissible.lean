-- Prove2me | solution 1 for PackingBounds.PackingBridge.sphere_packing_le_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/706df7fc-6931-470f-b9aa-092983a6fc13

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_geometricFactor_pos
import Theorems.Thm_LinearProgrammingBound
import Theorems.Thm_PackingBounds_PackingBridge_volume_half_ball

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology
open PackingBounds PackingBounds.PackingBridge
namespace PackingBounds.PackingBridge
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (f : CohnElkies.Admissible d) :
    SpherePackingConstant d ≤
      ENNReal.ofReal
        (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d * CohnElkies.quotient f) := by
  have hfne : f.function ≠ 0 := by
    intro hf
    have h := f.fourier_zero_pos
    rw [hf] at h
    simp at h
  have hreal : ∀ x : CohnElkies.Euclidean d,
      ((f.function x).re : ℂ) = f.function x := by
    intro x
    apply Complex.ext
    · simp
    · simp [f.real x]
  have hfourier : ∀ x : CohnElkies.Euclidean d,
      (((𝓕 f.function : CohnElkies.TestFunction d) x).re : ℂ) =
        (𝓕 f.function : CohnElkies.TestFunction d) x := by
    intro x
    apply Complex.ext
    · simp
    · simp [f.fourier_real x]
  have h := LinearProgrammingBound hfne hreal hfourier
    (fun x hx => f.outside_nonpos x hx) f.fourier_nonneg hd
  rw [volume_half_ball hd] at h
  have horigin : 0 ≤ (f.function (0 : CohnElkies.Euclidean d)).re :=
    (CohnElkies.admissible_zero_pos f).le
  have hratio :
      ((f.function (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) /
          (((𝓕 f.function : CohnElkies.TestFunction d)
            (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) =
        ENNReal.ofReal (CohnElkies.quotient f) := by
    rw [← ENNReal.coe_div (Real.toNNReal_pos.mpr f.fourier_zero_pos).ne']
    simp only [CohnElkies.quotient, ENNReal.ofReal,
      Real.toNNReal_div horigin]
  change SpherePackingConstant d ≤
    ((f.function (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) /
      (((𝓕 f.function : CohnElkies.TestFunction d)
        (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) *
      ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) at h
  rw [hratio] at h
  calc
    SpherePackingConstant d ≤
        ENNReal.ofReal (CohnElkies.quotient f) *
          ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) := h
    _ = ENNReal.ofReal
        (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d * CohnElkies.quotient f) := by
          rw [ENNReal.ofReal_mul (CohnElkies.geometricFactor_pos d).le]
          exact mul_comm _ _
end PackingBounds.PackingBridge
