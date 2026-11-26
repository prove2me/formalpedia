-- Prove2me | solution 1 for Sqrt6KissingBound.volume_rotationalProfile_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:22:20.794989+00:00
-- url     : https://prove2.me/submissions/049df175-bbd1-4163-917a-71a4c3df8299

import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_ProfileIntegral
import Theorems.Thm_Sqrt6KissingBound_volume_ball_eq_pow_mul_unit
import Theorems.Thm_Sqrt6KissingBound_volume_rotationalProfile


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped ENNReal Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 2))))
        (rotationalProfile (d + 1) (Set.Ioo a b) g) =
      ENNReal.ofReal (∫ t in a..b, g t ^ (d + 1)) *
        unitBallVolume (d + 1) := by
  rw [volume_rotationalProfile (d + 1) measurableSet_Ioo hg.measurable]
  simp_rw [volume_ball_eq_pow_mul_unit d]
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (g t) ^ (d + 1)) := by
    fun_prop
  rw [MeasureTheory.lintegral_mul_const (μ := volume.restrict (Set.Ioo a b))
    (unitBallVolume (d + 1)) hm]
  congr 1
  have hpow :
      (∫⁻ t in Set.Ioo a b, ENNReal.ofReal (g t) ^ (d + 1)) =
        ∫⁻ t in Set.Ioo a b, ENNReal.ofReal (g t ^ (d + 1)) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact (ENNReal.ofReal_pow (hg0 t ⟨ht.1.le, ht.2.le⟩) (d + 1)).symm
  rw [hpow]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hI : Integrable (fun t : ℝ => g t ^ (d + 1))
      (volume.restrict (Set.Ioc a b)) := by
    exact ((hg.pow (d + 1)).intervalIntegrable (μ := volume) a b).1
  have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), 0 ≤ g t ^ (d + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg (hg0 t ⟨ht.1.le, ht.2⟩) _
  rw [intervalIntegral.integral_of_le hab]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI hnn).symm
end Sqrt6KissingBound
