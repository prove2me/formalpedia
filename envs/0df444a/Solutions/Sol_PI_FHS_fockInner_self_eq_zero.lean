-- Prove2me | solution 1 for PI.FHS.fockInner_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:38.496056+00:00
-- url     : https://prove2.me/submissions/f528ecde-34d3-4c29-ae35-602d925575fa

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_wt_pos_nat
import Theorems.Thm_PI_FHS_fockInner_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution {P : MvPolynomial σ ℂ} (h : FockH1Action.fockInner P P = 0) : P = 0 := by
  have hre : ∑ α ∈ P.support, Complex.normSq (coeff α P) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) = 0 := by
    have h' := congrArg Complex.re h
    rw [fockInner_self, Complex.re_sum] at h'
    simpa only [Complex.ofReal_re, Complex.zero_re] using h'
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ => mul_nonneg (Complex.normSq_nonneg (coeff α P)) (Nat.cast_nonneg _))).mp hre
  by_contra hP
  obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hP)
  rcases mul_eq_zero.mp (hterm α hα) with h1 | h1
  · rw [Complex.normSq_eq_zero] at h1
    exact (MvPolynomial.mem_support_iff.mp hα) h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr (wt_pos_nat α).ne')
end PI.FHS
