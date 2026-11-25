-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isNormalSection_mul_cf8746bbf5eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:31.612843+00:00
-- url     : https://prove2.me/submissions/9f55d411-5951-4c54-ab4c-5eae37edd471

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_add_67d12914ee42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_div_chartPow_mem_9fad4a55970a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_mul_93013abb2ad1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_toFun_b8c3c6d4b863

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {a b : ι → ℤ} {s : P.FunField} (hs : P.IsNormalSection a s)
    (u : IntegralSection P b) : P.IsNormalSection (a + b) (s * u.toFun) :=
  ⟨isOfDegree_mul P hs.degree (isOfDegree_toFun P u), fun c hc ↦ by
    rw [chartPow_add P hc, mul_div_mul_comm]
    exact Subalgebra.mul_mem _ (hs.integral c hc)
      ((integralClosure (P.chartRing c) P.FunField).algebraMap_mem
        (⟨_, toFun_div_chartPow_mem P u hc⟩ : P.chartRing c))⟩
end GroundTheory.Heights₂.Heights.MonomialMapNorm
