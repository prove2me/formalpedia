-- Prove2me | solution 1 for PI.FJMX.tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:55.134168+00:00
-- url     : https://prove2.me/submissions/87d74af9-a10a-47cf-b418-7d10d9069a7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
namespace PI.FJMX
theorem _root_.solution (g : ℕ → ℕ) (hg : ∀ t, g (t + 1) ≤ g t) (i₀ : ℕ) (n : ℕ) :
    ∑ t ∈ Finset.range n, (if i₀ ≤ t then (g t - g (t + 1)) else 0) =
      if i₀ < n then g i₀ - g n else 0 := by
  have anti : Antitone g := antitone_nat_of_succ_le hg
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := hg n
    by_cases h : i₀ < n
    · have h2 : g n ≤ g i₀ := anti h.le
      rw [if_pos h, if_pos (by omega : i₀ ≤ n), if_pos (by omega : i₀ < n + 1)]
      omega
    · by_cases h' : i₀ = n
      · subst h'
        simp
      · rw [if_neg h, if_neg (by omega : ¬ i₀ ≤ n), if_neg (by omega : ¬ i₀ < n + 1)]
end PI.FJMX
