-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_evalCone_chartMonomial_ne_zero_0f3c784853ae
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:58.175904+00:00
-- url     : https://prove2.me/submissions/14f9110d-f14b-4dd2-bfc4-fa6d81849a40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38


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
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hz : ∀ k, z k (c k) ≠ 0) (e : ι → ℕ) : evalCone z (chartMonomial c e) ≠ 0 := by
  rw [evalCone_chartMonomial]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hz k)
end GroundTheory.Heights₂.Heights.ChartVanishing
