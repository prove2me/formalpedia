-- Prove2me | solution 1 for PI.WGB.FiltB_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:45.697724+00:00
-- url     : https://prove2.me/submissions/8f05d417-b2a4-4b1d-92a3-0da88d14d956

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB

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
theorem _root_.solution {σ : Type*} (ψ : σ → ℕ) {d d' : ℕ} (h : d' ≤ d) : FiltB ψ d ≤ FiltB ψ d' :=
  fun _ hp e he => le_trans h (hp e he)
end PI.WGB
