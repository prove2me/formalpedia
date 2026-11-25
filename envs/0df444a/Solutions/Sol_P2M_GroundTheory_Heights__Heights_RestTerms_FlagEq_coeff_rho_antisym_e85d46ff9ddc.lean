-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rho_antisym_e85d46ff9ddc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:29.444595+00:00
-- url     : https://prove2.me/submissions/ae1c1800-c945-408f-97e2-97fa8aa64750

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_inv_6fdc7c5857e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rename_prodCongrRight_58c6c769a27c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
variable {f N : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagEq
theorem _root_.solution {R : Type*} [CommRing R] (P : MvPolynomial (Fin f × Fin N) R) :
    coeff (rho f N) (∑ w : Fin f → Equiv.Perm (Fin N),
        ((permSign f N w : ℤ) : R) • rename (Equiv.prodCongrRight w) P) =
      ∑ w, ((permSign f N w : ℤ) : R) * coeff (stairExp f N w) P := by
  rw [coeff_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun w => ?_)
  rw [coeff_smul, smul_eq_mul, coeff_rename_prodCongrRight, Equiv.inv_apply, permSign_inv]
  congr 2
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
