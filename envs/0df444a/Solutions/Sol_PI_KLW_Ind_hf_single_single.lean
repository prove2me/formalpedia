-- Prove2me | solution 1 for PI.KLW.Ind.hf_single_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:04.789082+00:00
-- url     : https://prove2.me/submissions/a4e393f7-014e-4aa6-913d-a403f9f58e2a

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
theorem _root_.solution {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    [DecidableEq ι] (i0 : ι) : hf c (Pi.single i0 (1 : K)) (Pi.single i0 1) = 1 := by
  rw [hf_single_right, Pi.single_eq_same]
end PI.KLW.Ind
