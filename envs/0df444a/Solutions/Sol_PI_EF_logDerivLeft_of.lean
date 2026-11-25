-- Prove2me | solution 1 for PI.EF.logDerivLeft_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:53.411903+00:00
-- url     : https://prove2.me/submissions/4dc9faaf-288f-4cea-a571-a002db7f3738

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds
import Theorems.Thm_PI_EF_norm_logDeriv_le
import Theorems.Thm_PI_EF_log_two_le_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter
namespace PI.EF
theorem _root_.solution {Cw Cl : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hW : ZerosWindowWith Cw)
    (hL : LocalLemma Cl) (hZ : ZeroLocus) : LogDerivLeft (Cl + 2 * Cw + 6) := by
  unfold PI.EF.LogDerivLeft PI.EF.ZeroLocus at *
  intro N _ χ hχ t
  have hre : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re = -1 / 2 := by norm_num
  have him : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im = t := by norm_num
  have hne1 : ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro a
    have := congrArg Complex.re a
    rw [hre] at this
    norm_num at this
  have hL0 : LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h0
    rcases hZ N χ hχ _ (by rw [hre]; norm_num) hne1 h0 with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · rw [hre] at a
      norm_num at a
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
  have hs0 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ :=
    le_trans (by rw [hre]; norm_num) (Complex.abs_re_le_norm _)
  have hs1 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - 1‖ :=
    le_trans (by rw [Complex.sub_re, hre, Complex.one_re]; norm_num) (Complex.abs_re_le_norm _)
  have hnear : ∀ ρ ∈ ZerosNear χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im,
      1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, -⟩ := hρ
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, hre, abs_of_neg (by linarith)]
    linarith
  have key := norm_logDeriv_le hW hL χ hχ _ hre.symm.le (by rw [hre]; norm_num) hL0 hs0 hs1
    (by norm_num : (0 : ℝ) < 1 / 2) hnear
  rw [him] at key
  have hlog2 : Real.log 2 ≤ Real.log (N * (|t| + 2)) := log_two_le_log (by linarith [abs_nonneg t])
  have hl2 := Real.log_two_gt_d9
  refine le_trans key ?_
  calc Cl * Real.log (N * (|t| + 2)) + Cw * Real.log (N * (|t| + 2)) / (1 / 2) + 4
        = Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) + 4 := by ring
    _ ≤ Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) +
          6 * Real.log (N * (|t| + 2)) := by linarith
    _ = (Cl + 2 * Cw + 6) * Real.log (N * (|t| + 2)) := by ring
end PI.EF
