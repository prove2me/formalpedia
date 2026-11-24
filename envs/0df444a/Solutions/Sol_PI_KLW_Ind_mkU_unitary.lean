-- Prove2me | solution 1 for PI.KLW.Ind.mkU_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:56:00.92915+00:00
-- url     : https://prove2.me/submissions/fd950c2d-50f1-40d2-88db-ae20b7bd4bb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Theorems.Thm_PI_KLW_Ind_mkU_apply

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
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) :
    IsUnitary c (mkU c f hf') := fun v w => by
  rw [mkU_apply, mkU_apply]; exact hf' v w
end PI.KLW.Ind
