-- Prove2me | solution 1 for PI.KLW.hf_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:11.677555+00:00
-- url     : https://prove2.me/submissions/28b4958b-2063-4da5-a193-e71a9dde5c18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral

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
open PI PI.KLW
variable {K : Type} [Field K] {ι : Type} [Fintype ι] (c : K →+* K)
namespace PI.KLW
theorem _root_.solution (hc : ∀ x, c (c x) = x) (v w : ι → K) : hf c w v = c (hf c v w) := by
  simp only [hf, map_sum, map_mul, hc]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end PI.KLW
