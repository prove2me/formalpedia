-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_cons_zero_9549e2b329f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:35.010677+00:00
-- url     : https://prove2.me/submissions/9e87efff-dd20-44c7-b97d-b2671f89e061

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_cons_zero_c2d9a9f8b276
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_eventualValue_zero_2601218ff46a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (W : Ideal (MRing ι O)) {n : ℕ}
    (L : Fin n → K → ℤ) : vNum W (Matrix.vecCons 0 L) = 0 := by
  rw [vNum, intNum, mixedDiff_cons_zero, eventualValue_zero]
end GroundTheory.Heights₂.Heights.NumbersDVR
