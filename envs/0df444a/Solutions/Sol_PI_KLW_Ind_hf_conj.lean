-- Prove2me | solution 1 for PI.KLW.Ind.hf_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:40.562707+00:00
-- url     : https://prove2.me/submissions/ed21f80f-1cc7-44be-bca0-b87b6fbd4a4b

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
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) {ι : Type} [Fintype ι]
    (v w : ι → K) : c (hf c v w) = hf c w v := by
  simp only [hf, map_sum, map_mul, hc]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end PI.KLW.Ind
