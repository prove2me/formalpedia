-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_chartMonomial_ne_zero_f3bbdf95a0d6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:45.099877+00:00
-- url     : https://prove2.me/submissions/c4ad9790-5733-4626-8d74-02c81301edd3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt

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
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution (z : Cone n ℂ) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (hc : ∀ k, z k (c k) ≠ 0) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [chartMonomial, evalCone, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
end GroundTheory.Heights₂.Heights.MonomialMap
