-- Prove2me | solution 1 for PI.RhsWLim.W.RI.wb_posdef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:19.409862+00:00
-- url     : https://prove2.me/submissions/987d6184-4949-4c60-881c-1b172bd022b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvF
import Theorems.Thm_PI_RhsWLim_W_RI_herm_wb
import Theorems.Thm_PI_RhsWLim_W_RI_herm_hb
import Theorems.Thm_PI_RhsWLim_W_RI_herm_self_hb
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_inWb_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution {z d : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hd : inWb k r d)
    (hdz : herm (Hpk k r) d z = 0) (hdd : herm (Hpk k r) d d = 0) : d = 0 := by
  rw [herm_wb hd hz, herm_hb] at hdz
  rw [herm_wb hd hd, herm_self_hb] at hdd
  have hT' : 0 < Complex.normSq (wbPart k r z (Fin.last k)) -
      ∑ j : Fin k, Complex.normSq (wbPart k r z (Fin.castSucc j)) := by
    unfold Tz at hT
    rw [herm_wb hz hz, herm_self_hb, Complex.ofReal_re] at hT
    linarith
  set X : Fin k → ℂ := fun j => wbPart k r d (Fin.castSucc j)
  set Z : Fin k → ℂ := fun j => wbPart k r z (Fin.castSucc j)
  set xk := wbPart k r d (Fin.last k)
  set zk := wbPart k r z (Fin.last k)
  have hX : ∑ j, Complex.normSq (X j) = Complex.normSq xk := by
    have := Complex.ofReal_injective (hdd.trans Complex.ofReal_zero.symm)
    linarith
  have hdz' : star zk * xk = ∑ j, star (Z j) * X j := by
    rw [sub_eq_zero] at hdz
    exact hdz.symm
  have hxk : xk = 0 := by
    by_contra hne
    have h1 : ‖zk‖ * ‖xk‖ ≤ ∑ j, ‖Z j‖ * ‖X j‖ := by
      calc ‖zk‖ * ‖xk‖ = ‖star zk * xk‖ := by rw [norm_mul, norm_star]
        _ = ‖∑ j, star (Z j) * X j‖ := by rw [hdz']
        _ ≤ ∑ j, ‖star (Z j) * X j‖ := norm_sum_le _ _
        _ = ∑ j, ‖Z j‖ * ‖X j‖ := by simp only [norm_mul, norm_star]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖Z j‖) (fun j => ‖X j‖)
    have h3 : (‖zk‖ * ‖xk‖) ^ 2 ≤ (∑ j, ‖Z j‖ ^ 2) * (∑ j, ‖X j‖ ^ 2) :=
      (pow_le_pow_left₀ (by positivity) h1 2).trans h2
    simp only [← Complex.normSq_eq_norm_sq] at h3
    rw [hX, mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h3
    have hpos : 0 < Complex.normSq xk := Complex.normSq_pos.2 hne
    nlinarith
  have hX0 : ∀ j, X j = 0 := by
    intro j
    rw [hxk, map_zero] at hX
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (X j))).1 hX j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hb : wbPart k r d = 0 := by
    ext m
    induction m using Fin.lastCases with
    | last => exact hxk
    | cast j => exact hX0 j
  rw [← inWb_eq hd, hb, Matrix.mulVec_zero]
end PI.RhsWLim.W.RI
