-- Prove2me | solution 1 for PI.Residue.classLower_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:54.357881+00:00
-- url     : https://prove2.me/submissions/96738cd1-dfe1-4563-a10c-59fb196cda85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BClass
import Theorems.Thm_PI_Residue_vfac_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution (hCI : CountIntegral) (hSV : ShellVolume) (hU : Unfold) (hH : HitBound)
    (hI : IdealSetSum) : ClassLower := by
  intro K _ _ s C hs
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  set m := Module.finrank ℚ K with hm
  have hm0 : 0 < m := Module.finrank_pos
  set D : ℝ := ((|discr K| : ℤ) : ℝ) with hD
  have hD0 : 0 < D := by
    have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs (discr_ne_zero K)
    have : (1 : ℝ) ≤ D := by rw [hD]; exact_mod_cast this
    linarith
  have hsq : 0 < √D := Real.sqrt_pos.mpr hD0
  set N : ℝ := (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) with hN
  have hN0 : 0 < N := Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors J)
  set P : ℝ := 2 * √D * N with hP
  have hP0 : 0 < P := by positivity
  set ρ : ℝ := P ^ ((1 : ℝ) / m) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hP0 _
  have hρm : ρ ^ m = P := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le, one_div,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm0.ne'), Real.rpow_one]
  have hcov : ZLattice.covolume (lat K J) = N * 2⁻¹ ^ nrComplexPlaces K * √D := by
    rw [covolume_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
      Rat.cast_natCast, ← Int.cast_abs]
  have hcov0 : 0 < ZLattice.covolume (lat K J) := by rw [hcov]; positivity
  set c := ENNReal.ofReal (ZLattice.covolume (lat K J)) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.mpr hcov0).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hv0 : vfac K ≠ 0 := by
    rw [vfac_eq]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hvT : vfac K ≠ ⊤ := by rw [vfac_eq]; exact ENNReal.ofReal_ne_top
  set S := volume (shell K) with hS
  have hSe : S = vfac K * ENNReal.ofReal (regulator K) / 2 := hSV K
  have hST : S ≠ ⊤ := by
    rw [hSe]
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top hvT ENNReal.ofReal_ne_top) (by norm_num)
  set T := ∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K)) with hT
  have h1 : vfac K * ENNReal.ofReal ((ρ / 2) ^ m) * S ≤ T * c := hCI K J ρ hρ0
  have h2 : 2 * c ≤ vfac K * ENNReal.ofReal ((ρ / 2) ^ m) := by
    rw [vfac_eq, ← ENNReal.ofReal_mul (by positivity), hc,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [hcov, div_pow, hρm, hP, hm, ← card_add_two_mul_card_eq_rank K, pow_add, pow_mul]
    have h4 : (2⁻¹ : ℝ) ^ nrComplexPlaces K ≤ (Real.pi / 4) ^ nrComplexPlaces K :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) _
    have e : (2 : ℝ) ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K *
        (2 * √D * N / (2 ^ nrRealPlaces K * (2 ^ 2) ^ nrComplexPlaces K)) =
        2 * (N * (Real.pi / 4) ^ nrComplexPlaces K * √D) := by
      rw [div_pow]; norm_num; field_simp
    rw [e]
    gcongr
  have h3 : 2 * S ≤ T := by
    have : 2 * S * c ≤ T * c := by
      calc 2 * S * c = 2 * c * S := by ring
        _ ≤ vfac K * ENNReal.ofReal ((ρ / 2) ^ m) * S := by gcongr
        _ ≤ T * c := h1
    exact (ENNReal.mul_le_mul_iff_left hc0 hcT).1 this
  set Z : ℝ≥0∞ := ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
    ((torsionOrder K : ℝ≥0∞) * ENNReal.ofReal (N ^ (-s)) * classZeta K C s) with hZ
  have h4 : T ≤ S + vfac K * Z := by
    refine (hU K J ρ hρ0).trans ?_
    gcongr
    calc ∑' x : idealSet K J,
          volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K))
        ≤ ∑' x : idealSet K J, vfac K * (ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
            ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          have := hH K ρ s (x : mixedSpace K) hρ0 hs (norm_pos_of_mem x.2.1)
          rwa [← hm, hρm, ENNReal.ofReal_mul (by positivity)] at this
      _ = vfac K * (ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
            ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ vfac K * Z := by
          rw [hZ]; gcongr; exact hI K s C J hJ
  have h5 : S ≤ vfac K * Z := by
    have : S + S ≤ S + vfac K * Z := by rw [← two_mul]; exact h3.trans h4
    exact (ENNReal.add_le_add_iff_left hST).1 this
  have h6 : ENNReal.ofReal (regulator K) ≤ 2 * Z := by
    rw [hSe, ENNReal.div_le_iff (by norm_num) (by norm_num), mul_assoc] at h5
    have := (ENNReal.mul_le_mul_iff_right hv0 hvT).1 h5
    rwa [mul_comm] at this
  refine h6.trans (le_of_eq ?_)
  rw [hZ, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e1 : 2 * (P * (2 * P) ^ (s - 1)) = (2 * P) ^ s := by
    rw [← mul_assoc]
    nth_rewrite 1 [← Real.rpow_one (2 * P)]
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have e2 : (2 * P) ^ s * N ^ (-s) = 4 ^ s * D ^ (s / 2) := by
    have : 2 * P = 4 * √D * N := by rw [hP]; ring
    rw [this, Real.mul_rpow (by positivity) hN0.le, Real.mul_rpow (by norm_num) hsq.le, mul_assoc,
      ← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero, mul_one, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hD0.le]
    congr 2; ring
  rw [e1, mul_right_comm, e2]
end PI.Residue
