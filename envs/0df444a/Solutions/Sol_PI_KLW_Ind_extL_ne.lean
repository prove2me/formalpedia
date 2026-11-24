-- Prove2me | solution 1 for PI.KLW.Ind.extL_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:03.950611+00:00
-- url     : https://prove2.me/submissions/f3f0e1ff-ff6c-4dfd-a0d3-69018fdeeb1f

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
    (w : {i // i ≠ i0} → K) (j : {i // i ≠ i0}) : extL i0 w j.1 = w j := by
  simp [extL, j.2]
end PI.KLW.Ind
