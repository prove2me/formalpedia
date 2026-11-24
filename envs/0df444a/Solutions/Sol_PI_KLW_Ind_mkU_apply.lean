-- Prove2me | solution 1 for PI.KLW.Ind.mkU_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:36.302027+00:00
-- url     : https://prove2.me/submissions/1574d297-e6db-4633-a36e-ce2819ba9c77

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
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) (v : ι → K) :
    mkU c f hf' v = f v := by
  unfold mkU
  rw [LinearEquiv.coe_ofInjectiveEndo]
end PI.KLW.Ind
