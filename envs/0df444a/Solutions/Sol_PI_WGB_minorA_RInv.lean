-- Prove2me | solution 1 for PI.WGB.minorA_RInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:48.274005+00:00
-- url     : https://prove2.me/submissions/0bcf8914-426e-4194-b7b9-d6a3842128e2

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_minor_RInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (s : ℕ) (hr : s ≤ n + 1) :
    RInvA (fun x : Fin (n + 1) × Fin (n + 1) → ℂ => eval x (lpMinor ℂ s hr hr)) :=
  fun x a b t hab _ => lhwline_minor_RInv s hr hr x a b t hab
end PI.WGB
