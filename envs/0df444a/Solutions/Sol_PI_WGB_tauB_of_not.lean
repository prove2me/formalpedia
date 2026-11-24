-- Prove2me | solution 1 for PI.WGB.tauB_of_not
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:30.500202+00:00
-- url     : https://prove2.me/submissions/bf017d8c-10bd-4406-9272-9417faf7cb80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB

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
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) (ha : ¬ a.1 < n) :
    tauB h σ a = a := by
  unfold tauB; rw [dif_neg ha]
end PI.WGB
