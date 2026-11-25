-- Prove2me | solution 1 for UpperTheory.map_left_mul_volume_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:38.057806+00:00
-- url     : https://prove2.me/submissions/06ead58c-f5ab-4910-8dd5-9f7cc9a84062

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapLeftMulVolumeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.det_leftMulLinearMap (n : ℕ) (a : Fin n → Fin n → ℂ) :
    LinearMap.det (UpperTheory.matrixLeftMulLinearMap n a) = (Matrix.of a).det ^ n := by
  unfold UpperTheory.matrixLeftMulLinearMap
  rw [LinearMap.det_conj, LinearMap.det_pi]
  simp
end

set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (n : ℕ) (a : Fin n → Fin n → ℂ), ‖(Matrix.of a).det‖ = 1 →
        MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)) = MeasureTheory.volume := by
  intro n a ha
  have hf : (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
      = ⇑((UpperTheory.matrixLeftMulLinearMap n a).restrictScalars ℝ) := by
    funext x i j
    rfl
  have hd : LinearMap.det ((UpperTheory.matrixLeftMulLinearMap n a).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, UpperTheory.det_leftMulLinearMap, Algebra.norm_complex_apply, map_pow,
      Complex.normSq_eq_norm_sq, ha]
    simp
  haveI h1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI h2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  rw [hf, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar _
    (by rw [hd]; exact one_ne_zero), hd]
  simp
end UpperTheory
