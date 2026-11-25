-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial_ne_zero_cbad317c02fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:07.18932+00:00
-- url     : https://prove2.me/submissions/98091edb-dc04-48f2-8a7c-111363aeb62f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial__4bb3055a91f9

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)} (d : ι → ℕ)
    (hc : ∀ k, z k (c k) ≠ 0) : evalCone z (chartMonomial c d) ≠ 0 := by
  rw [evalCone_chartMonomial']
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
end GroundTheory.Heights₂.Heights.BoundedMonomials
