-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.mem_irrDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:28.932336+00:00
-- url     : https://prove2.me/submissions/b14d7d45-1873-4517-bc23-5871fb97ae55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Theorems.Thm_PI_SqfPrimeFactor_W_mem_monicDeg

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
variable {g : ℕ} [Fact g.Prime]
open Classical
namespace PI.SqfPrimeFactor.W
theorem _root_.solution {d : ℕ} {q : (ZMod g)[X]} :
    q ∈ irrDeg g d ↔ (q.Monic ∧ q.natDegree = d) ∧ Irreducible q := by
  unfold irrDeg
  rw [Finset.mem_filter, mem_monicDeg]
end PI.SqfPrimeFactor.W
