-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_perm_129463b0e566
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:55.695039+00:00
-- url     : https://prove2.me/submissions/39957492-1f8a-4da9-b4d4-5ef1fc38f2b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_rename_7a95f98ac519
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sign_mul_self_630c9b7c6f03

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
theorem _root_.solution {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m)) (v : Fin m → ℕ) :
    cf (v ∘ σ.symm) P = ((Perm.sign σ : ℤ) : ℚ) * cf v P := by
  have h := cf_rename v σ P
  rw [hP σ] at h
  unfold cf at h ⊢
  rw [coeff_smul, zsmul_eq_mul] at h
  rw [← h, ← mul_assoc, sign_mul_self, one_mul]
end GroundTheory.Heights₂.Heights.RestTerms.Comb
