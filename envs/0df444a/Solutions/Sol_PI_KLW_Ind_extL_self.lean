-- Prove2me | solution 1 for PI.KLW.Ind.extL_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:10.450125+00:00
-- url     : https://prove2.me/submissions/9d47a41f-9c74-4f5a-9ce9-6e1e63798367

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction

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
theorem _root_.solution {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι)
    (w : {i // i ≠ i0} → K) : extL i0 w i0 = 0 := by
  simp [extL]
end PI.KLW.Ind
