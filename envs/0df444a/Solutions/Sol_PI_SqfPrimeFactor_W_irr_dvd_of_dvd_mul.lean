-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.irr_dvd_of_dvd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:58.136561+00:00
-- url     : https://prove2.me/submissions/00fd94b9-02d6-47a8-a3b3-a12e9be5280e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate

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
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfPrimeFactor.W
theorem _root_.solution {q q' h : (ZMod g)[X]} (hq : Irreducible q) (hh : h ≠ 0)
    (hdeg : h.natDegree < q.natDegree) (hd : q ∣ q' * h) : q ∣ q' := by
  rcases hq.prime.dvd_or_dvd hd with h1 | h1
  · exact h1
  · exact absurd (natDegree_le_of_dvd h1 hh) (not_le.2 hdeg)
end PI.SqfPrimeFactor.W
