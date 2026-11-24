-- Prove2me | solution 1 for PI.KLW.hf_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:20.474698+00:00
-- url     : https://prove2.me/submissions/178aac6f-b765-4d74-b0c2-67e11a1c922e

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
theorem _root_.solution (v v' w : ι → K) : hf c (v + v') w = hf c v w + hf c v' w := by
  simp [hf, add_mul, Finset.sum_add_distrib]
end PI.KLW
