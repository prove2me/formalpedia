-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_eq_sum_69324f4b2849
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:22:13.531842+00:00
-- url     : https://prove2.me/submissions/8c4e7912-ff82-4f18-8302-dd0b8f7f52a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (v : Fin m → ℕ) :
    alt v = ∑ σ : Perm (Fin m), (Perm.sign σ : ℤ) • monomial (ex (v ∘ σ.symm)) (1 : ℚ) := by
  unfold alt
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  simp only [Matrix.of_apply]
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  exact Fintype.prod_equiv σ _ _ (fun i => by simp)
end GroundTheory.Heights₂.Heights.RestTerms.Comb
