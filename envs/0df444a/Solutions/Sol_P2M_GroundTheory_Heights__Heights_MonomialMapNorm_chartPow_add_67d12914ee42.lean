-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_add_67d12914ee42
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:44.080364+00:00
-- url     : https://prove2.me/submissions/e202c5a9-52e1-4244-9d90-c14c3f3a6cb1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_X_ne_zero_610853a0b298

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
theorem _root_.solution {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a b : ι → ℤ) :
    P.chartPow c (a + b) = P.chartPow c a * P.chartPow c b := by
  rw [ArithVariety.chartPow, ArithVariety.chartPow, ArithVariety.chartPow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ ↦ by rw [Pi.add_apply, zpow_add₀ (mkF_X_ne_zero P hc k)]
end GroundTheory.Heights₂.Heights.MonomialMapNorm
