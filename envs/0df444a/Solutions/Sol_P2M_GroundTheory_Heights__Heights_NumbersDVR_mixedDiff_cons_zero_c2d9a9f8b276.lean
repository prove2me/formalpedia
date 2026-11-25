-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_cons_zero_c2d9a9f8b276
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:34.428474+00:00
-- url     : https://prove2.me/submissions/0fcdc79e-84bd-405c-9fac-ee925b93f87e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero

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
theorem _root_.solution {K : Type*} {n : ℕ} (L : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Matrix.vecCons 0 L) h = 0 := by
  unfold mixedDiff
  rw [List.ofFn_succ, List.foldr_cons, Matrix.cons_val_zero]
  funext m
  simp [diffStep]
end GroundTheory.Heights₂.Heights.NumbersDVR
