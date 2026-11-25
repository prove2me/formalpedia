-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_C_mul_prod_linForm_3831a9c346e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:43.477592+00:00
-- url     : https://prove2.me/submissions/4d681603-7766-4b81-abfa-f334ffa1110a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
omit [DecidableEq Ψ]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
theorem _root_.solution (c : ℚ) {d : ℕ} (ℓ : Fin d → Ψ × Fin N → ℤ) :
    (C c * ∏ i, linForm Ψ N (ℓ i) : RootPoly Ψ N) =
      ∑ r : Fin d → Ψ × Fin N, monomial (∑ i, Finsupp.single (r i) 1) (c * ∏ i, (ℓ i (r i) : ℚ)) := by
  unfold linForm
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← C_mul_monomial]
  congr 1
  rw [show (∏ i, (ℓ i (r i) : ℚ)) = (∏ i, (ℓ i (r i) : ℚ)) * 1 from (mul_one _).symm, ← C_mul_monomial,
    monomial_sum_one]
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  rfl
end GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
