-- Prove2me | solution 1 for PI.KLW.Ind.unitary_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:07.510538+00:00
-- url     : https://prove2.me/submissions/da04a158-d80f-4d25-b86a-97c88fe41260

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
theorem _root_.solution {K : Type} [Field K] {c : K →+* K} {ι : Type} [Fintype ι]
    {u u' : (ι → K) ≃ₗ[K] (ι → K)} (hu : IsUnitary c u) (hu' : IsUnitary c u') :
    IsUnitary c (u.trans u') := fun v w => by
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hu', hu]
end PI.KLW.Ind
