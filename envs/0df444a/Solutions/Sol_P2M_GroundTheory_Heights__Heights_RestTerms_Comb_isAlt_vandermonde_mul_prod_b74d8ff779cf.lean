-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isAlt_vandermonde_mul_prod_b74d8ff779cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:03.126948+00:00
-- url     : https://prove2.me/submissions/c62b9a92-d6db-410e-9374-9504110e8c4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_isAlt_9f813e5016fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_X_eq_alt_52fd29888339
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_mul_symm_37e73d51bc65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isSymmetric_prod_psum_0553020b3d1e

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
theorem _root_.solution (ρ : List ℕ) :
    IsAlt (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) *
      (ρ.map fun q => psum (Fin m) ℚ q).prod) := by
  rw [vandermondeOf_X_eq_alt]
  exact (alt_isAlt _).mul_symm (isSymmetric_prod_psum ρ)
end GroundTheory.Heights₂.Heights.RestTerms.Comb
