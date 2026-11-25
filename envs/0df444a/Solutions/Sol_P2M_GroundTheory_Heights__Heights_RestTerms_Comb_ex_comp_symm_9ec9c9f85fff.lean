-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_ex_comp_symm_9ec9c9f85fff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:16.110032+00:00
-- url     : https://prove2.me/submissions/8502d27f-4b7d-42c8-a500-f5319dd56710

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
theorem _root_.solution (v : Fin m → ℕ) (σ : Perm (Fin m)) :
    Finsupp.mapDomain σ (ex v) = ex (v ∘ σ.symm) := by
  ext i
  conv_lhs => rw [← σ.apply_symm_apply i]
  rw [Finsupp.mapDomain_apply σ.injective]
  simp
end GroundTheory.Heights₂.Heights.RestTerms.Comb
