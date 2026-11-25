-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_killBlocks_compl_rename_cd9002839356
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:08.717881+00:00
-- url     : https://prove2.me/submissions/99616cfa-6c1d-41b6-bb31-382f7c4d946c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_X_a86018fe216d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {F : Type*}
  [Field F] (j : K ↪ K') (ι' : K' → Type*)
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
theorem _root_.solution :
    (killBlocks (ι := ι') (F := F) (Finset.univ.map j)ᶜ).comp (rename (blockIncl j ι')) =
      rename (blockIncl j ι') := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [killBlocks_X, blockIncl]
end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
