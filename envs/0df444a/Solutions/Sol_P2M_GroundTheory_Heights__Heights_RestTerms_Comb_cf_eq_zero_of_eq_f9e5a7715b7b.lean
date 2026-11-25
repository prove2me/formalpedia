-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_eq_zero_of_eq_f9e5a7715b7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:29.775804+00:00
-- url     : https://prove2.me/submissions/478161ab-694a-4610-8f0e-e7fb787c7737

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_perm_129463b0e566

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
theorem _root_.solution {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) {v : Fin m → ℕ} {i j : Fin m}
    (hij : i ≠ j) (h : v i = v j) : cf v P = 0 := by
  have h1 := cf_perm hP (Equiv.swap i j) v
  have h2 : v ∘ (Equiv.swap i j).symm = v := by
    funext k
    simp only [Function.comp_apply, Equiv.symm_swap]
    rcases eq_or_ne k i with rfl | hki
    · simp [h]
    rcases eq_or_ne k j with rfl | hkj
    · simp [h]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [h2, Perm.sign_swap hij] at h1
  simp at h1
  linarith
end GroundTheory.Heights₂.Heights.RestTerms.Comb
