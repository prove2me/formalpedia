-- Prove2me | solution 1 for PI.KLW.Ind.hf_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:43.290468+00:00
-- url     : https://prove2.me/submissions/23adceb2-2a0e-4243-9ba3-a90f3caf8e7e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w : ι → K) :
    hf c v (-w) = -hf c v w := by
  simp only [hf, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
end PI.KLW.Ind
