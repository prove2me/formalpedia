-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_eq_sum_5b30b6969504
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:05.731602+00:00
-- url     : https://prove2.me/submissions/db3a891f-6273-4e6c-b6e3-fa027bb8b3c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion

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
open GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
namespace GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
theorem _root_.solution {r : ℕ} (f : Fin r → Fin r ⊕ Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename f G = ∑ μ ∈ G.support, C (G.coeff μ) * ∏ j, X (f j) ^ μ j := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), map_mul, rename_C, map_prod]
  simp [map_pow, rename_X]
end GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
