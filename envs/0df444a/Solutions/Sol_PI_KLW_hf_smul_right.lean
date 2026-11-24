-- Prove2me | solution 1 for PI.KLW.hf_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:54.512657+00:00
-- url     : https://prove2.me/submissions/153bf93b-568c-4037-9ed9-b53bf3e76248

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
theorem _root_.solution (a : K) (v w : ι → K) : hf c v (a • w) = c a * hf c v w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
end PI.KLW
