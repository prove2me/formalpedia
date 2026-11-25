-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_proof_ede43e0d059c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:53.318007+00:00
-- url     : https://prove2.me/submissions/2060121e-9eb8-4ed7-b64f-4def93b08e2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_perm_42358017be47
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_update_add_cc0e459b4cb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_exists_eventually_const_1a8f49af4e5a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace MixedNumberPolynomial
theorem _root_.solution (h : MultigradedHilbertPolynomial.Statement.{u}) :
    MixedNumberPolynomial.Statement.{u} := by
  intro F _ K _ _ ι _ q d hq hdim
  exact ⟨fun σ bs => MixedNumberPolynomial.intNum_perm F q σ bs,
    fun bs j x y => MixedNumberPolynomial.intNum_update_add F q
      (MixedNumberPolynomial.exists_eventually_const h F K ι q d hq hdim) bs j x y⟩
end MixedNumberPolynomial
end GroundTheory.Heights₂.Heights.HilbertSamuel
