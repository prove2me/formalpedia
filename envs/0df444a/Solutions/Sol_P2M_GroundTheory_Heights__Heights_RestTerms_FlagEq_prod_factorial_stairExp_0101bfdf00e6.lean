-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_prod_factorial_stairExp_0101bfdf00e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:26.629617+00:00
-- url     : https://prove2.me/submissions/d01f1ccb-b0f9-48ae-9377-d1c12f192541

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight

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
theorem _root_.solution (w : Fin f → Equiv.Perm (Fin N)) :
    (stairExp f N w).prod (fun _ e => (e.factorial : ℝ)) = stairConst f N := by
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type]
  have h : ∀ τ, ∏ i : Fin N, ((stairExp f N w (τ, i)).factorial : ℝ) =
      ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) := by
    intro τ
    simp only [stairExp, Finsupp.coe_equivFunOnFinite_symm]
    exact Equiv.prod_comp (w τ).symm (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ))
  rw [prod_congr rfl (fun τ _ => h τ), prod_const, card_univ, Fintype.card_fin, stairConst]
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
