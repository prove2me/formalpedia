-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.claim_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:14.647829+00:00
-- url     : https://prove2.me/submissions/ddbfb4bf-56f2-4c7a-8a7b-dedccb984732

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_ClaimOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open PI.SqfLab
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (hA : CountA) (hB : IrrLower) (hC : Analytic) : PI.SqfPrimeFactor.Claim := by
  intro g r _ hr hg T hT
  refine (hA g r T hT).trans (le_trans ?_ (hC g r hr hg))
  gcongr with p hp
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [div_le_iff₀ hp0]
  have := hB g p hpp
  linarith
end PI.SqfPrimeFactor.W
