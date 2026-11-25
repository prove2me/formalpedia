-- Prove2me | solution 1 for PI.SSE.latExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:34.206059+00:00
-- url     : https://prove2.me/submissions/13b8845c-e765-4f05-93be-bacd9dadb61d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt
import Theorems.Thm_PI_SSE_qf_zero
import Theorems.Thm_PI_SSE_rel_neg
import Theorems.Thm_PI_SSE_rel_comb
import Theorems.Thm_PI_SSE_psi_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution : LatExt := by
  intro v₁ v₂ hpos G h₁ h₂ ω hω z
  have hne : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0 := hpos.ne'
  have hA : ((((starRingEnd ℂ) v₁ * v₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  have hI : (starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂ =
      2 * I * ((((starRingEnd ℂ) v₁ * v₂).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  set A : ℂ := ((((starRingEnd ℂ) v₁ * v₂).im : ℝ) : ℂ) with hAdef
  have r10 : Rel G A v₁ v₂ 1 0 := by
    intro z
    have e : ((1 : ℤ) : ℂ) * v₁ + ((0 : ℤ) : ℂ) * v₂ = v₁ := by push_cast; ring
    rw [e, h₁ z]
    norm_num
  have r01 : Rel G A v₁ v₂ 0 1 := by
    intro z
    have e : ((0 : ℤ) : ℂ) * v₁ + ((1 : ℤ) : ℂ) * v₂ = v₂ := by push_cast; ring
    rw [e, h₂ z]
    norm_num
  have r00 : Rel G A v₁ v₂ 0 0 := by
    intro z
    simp [qf_zero]
  have rm10 : Rel G A v₁ v₂ (-1) 0 := by
    intro z
    have hn := rel_neg G A v₁ (-1) (-1) hA (by norm_num) (fun z => by rw [h₁ z]; ring) z
    have e : ((-1 : ℤ) : ℂ) * v₁ + ((0 : ℤ) : ℂ) * v₂ = -v₁ := by push_cast; ring
    rw [e, hn]
    norm_num
  have r0m1 : Rel G A v₁ v₂ 0 (-1) := by
    intro z
    have hn := rel_neg G A v₂ (-1) (-1) hA (by norm_num) (fun z => by rw [h₂ z]; ring) z
    have e : ((0 : ℤ) : ℂ) * v₁ + ((-1 : ℤ) : ℂ) * v₂ = -v₂ := by push_cast; ring
    rw [e, hn]
    norm_num
  have hcol : ∀ m : ℤ, Rel G A v₁ v₂ m 0 := by
    intro m
    refine Int.induction_on m r00 (fun i hi => ?_) (fun i hi => ?_)
    · have h := rel_comb G A v₁ v₂ hA hI _ _ _ _ hi r10
      convert h using 2 <;> omega
    · have h := rel_comb G A v₁ v₂ hA hI _ _ _ _ hi rm10
      convert h using 2 <;> omega
  have hall : ∀ m n : ℤ, Rel G A v₁ v₂ m n := by
    intro m n
    refine Int.induction_on n (hcol m) (fun i hi => ?_) (fun i hi => ?_)
    · have h := rel_comb G A v₁ v₂ hA hI _ _ _ _ hi r01
      convert h using 2 <;> omega
    · have h := rel_comb G A v₁ v₂ hA hI _ _ _ _ hi r0m1
      convert h using 2 <;> omega
  have hω' := hω
  unfold PI.lat2 at hω'
  obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.mp hω'
  have e : m • v₁ + n • v₂ = (m : ℂ) * v₁ + n * v₂ := by rw [zsmul_eq_mul, zsmul_eq_mul]
  rw [e, ← psi_eq v₁ v₂ hne m n]
  exact hall m n z
end PI.SSE
