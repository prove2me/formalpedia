-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.irr_mem_monicDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:17.971841+00:00
-- url     : https://prove2.me/submissions/f38c799c-3fdd-4288-ab5d-a0dc05686b0c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_IrreducibleCountLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
namespace PI.SqfPrimeFactor.W
theorem _root_.solution {g d : ℕ} [Fact g.Prime] {q : (ZMod g)[X]} (hq : q.Monic)
    (hd : q.natDegree = d) : q ∈ monicDeg g d := by
  unfold monicDeg
  rw [Finset.mem_image]
  refine ⟨fun i => q.coeff i, Finset.mem_univ _, ?_⟩
  subst hd
  rw [Fin.sum_univ_eq_sum_range (fun i => C (q.coeff i) * X ^ i) q.natDegree]
  exact hq.as_sum.symm
end PI.SqfPrimeFactor.W
