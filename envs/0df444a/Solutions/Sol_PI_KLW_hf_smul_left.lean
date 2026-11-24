-- Prove2me | solution 1 for PI.KLW.hf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:11.027153+00:00
-- url     : https://prove2.me/submissions/93267d45-1712-47c9-a1a1-478ab46538a9

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
theorem _root_.solution (a : K) (v w : ι → K) : hf c (a • v) w = a * hf c v w := by
  simp [hf, Finset.mul_sum, mul_assoc]
end PI.KLW
