-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_chartMonomial_ne_zero_74ae91588762
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:44.486801+00:00
-- url     : https://prove2.me/submissions/38e953ea-1ad4-4f93-a349-74e424f77adb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis

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
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hcz : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [chartMonomial, evalCone, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hcz k)
end GroundTheory.Heights₂.Heights.MonomialMapNorm
