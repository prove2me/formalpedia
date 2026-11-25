-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_rename_7a95f98ac519
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:26:09.808083+00:00
-- url     : https://prove2.me/submissions/7eb65679-6e89-46e8-bc9c-86874f90a9a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_ex_comp_symm_9ec9c9f85fff

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
theorem _root_.solution (v : Fin m → ℕ) (σ : Perm (Fin m)) (P : MvPolynomial (Fin m) ℚ) :
    cf (v ∘ σ.symm) (rename σ P) = cf v P := by
  unfold cf
  rw [← ex_comp_symm, coeff_rename_mapDomain _ σ.injective]
end GroundTheory.Heights₂.Heights.RestTerms.Comb
