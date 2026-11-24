-- Prove2me | solution 1 for PI.KLW.Ind.hf_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:05.005854+00:00
-- url     : https://prove2.me/submissions/cf76a312-40e5-4eea-9c8e-bdda8bb63506

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
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w w' : ι → K) :
    hf c v (w + w') = hf c v w + hf c v w' := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end PI.KLW.Ind
