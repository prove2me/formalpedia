-- Prove2me | solution 1 for PI.KLW.hf_single_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:22.713448+00:00
-- url     : https://prove2.me/submissions/6f2d8388-4a2e-4a2c-8ea4-b6ed261d22b1

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
theorem _root_.solution [DecidableEq ι] (i : ι) (a : K) (w : ι → K) :
    hf c (Pi.single i a) w = a * c (w i) := by
  simp [hf, Pi.single_apply]
end PI.KLW
