-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_zero_of_cf_ddde2895fcf8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:22:52.136247+00:00
-- url     : https://prove2.me/submissions/15837dbf-36d1-4467-92dc-23e14fe75958

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_perm_129463b0e566
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_eq_zero_of_eq_f9e5a7715b7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_exists_perm_strictAnti_2971ced7b813

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
namespace IsAlt
theorem _root_.solution {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P)
    (h : ∀ l : Fin m → ℕ, StrictAnti l → cf l P = 0) : P = 0 := by
  ext d
  rw [coeff_zero]
  have hd : coeff d P = cf (⇑d) P := by unfold cf; simp
  rw [hd]
  by_cases hinj : Function.Injective (⇑d)
  · obtain ⟨σ, hσ⟩ := exists_perm_strictAnti hinj
    have h1 := cf_perm hP σ (⇑d ∘ σ)
    have h2 : (⇑d ∘ σ) ∘ σ.symm = ⇑d := by funext i; simp
    rw [h2, h _ hσ, mul_zero] at h1
    exact h1
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    exact cf_eq_zero_of_eq hP hne hij
end IsAlt
end GroundTheory.Heights₂.Heights.RestTerms.Comb
