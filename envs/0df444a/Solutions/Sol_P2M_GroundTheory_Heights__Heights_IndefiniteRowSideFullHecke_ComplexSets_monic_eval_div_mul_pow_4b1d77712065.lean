-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_eval_div_mul_pow_4b1d77712065
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:28.07841+00:00
-- url     : https://prove2.me/submissions/36847096-244e-4e3a-bbcc-51a486a140bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalBoundedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalBoundedQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {d : ℕ} (a : Fin d → ℂ) {F G : ℂ} (hG : G ≠ 0) :
    F ^ d + ∑ j : Fin d, a j * F ^ (j : ℕ) * G ^ (d - (j : ℕ)) =
      G ^ d * ((F / G) ^ d + ∑ j : Fin d, a j * (F / G) ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hG)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ d := j.isLt.le
  have hGd : G ^ d = G ^ (j : ℕ) * G ^ (d - (j : ℕ)) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hGd, div_pow]
  field_simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
