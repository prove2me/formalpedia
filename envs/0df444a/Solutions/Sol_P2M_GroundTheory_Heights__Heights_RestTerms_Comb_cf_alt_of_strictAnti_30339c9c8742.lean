-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_of_strictAnti_30339c9c8742
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:24.391232+00:00
-- url     : https://prove2.me/submissions/dc2979a8-e872-48fe-9eb8-4a708c41bfc3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_9541255e1ef5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_perm_eq_one_of_strictAnti_b6a2e97b94d9

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
theorem _root_.solution {l v : Fin m → ℕ} (hl : StrictAnti l) (hv : StrictAnti v) :
    cf l (alt v) = if l = v then 1 else 0 := by
  rw [cf_alt, Finset.sum_eq_single (1 : Perm (Fin m))]
  · have h1 : v ∘ ⇑(Equiv.symm (1 : Perm (Fin m))) = v := rfl
    simp [h1]
  · intro σ _ hσ
    rw [if_neg, mul_zero]
    intro h
    apply hσ
    have : σ.symm = 1 := by
      apply perm_eq_one_of_strictAnti hv
      rw [← h]; exact hl
    rw [← Equiv.symm_symm σ, this]; rfl
  · simp
end GroundTheory.Heights₂.Heights.RestTerms.Comb
