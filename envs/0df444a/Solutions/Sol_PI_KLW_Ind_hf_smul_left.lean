-- Prove2me | solution 1 for PI.KLW.Ind.hf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:45:02.330448+00:00
-- url     : https://prove2.me/submissions/80c8f951-3cfb-4f10-b60a-73ce48b9a3de

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
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (k : K)
    (v w : ι → K) : hf c (k • v) w = k * hf c v w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
end PI.KLW.Ind
