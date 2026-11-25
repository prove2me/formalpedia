-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_killStable_2361f4b4da88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:59.001144+00:00
-- url     : https://prove2.me/submissions/61e48850-acf0-4b32-8715-79e753be53ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_killBlocks_55558e3754dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa


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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution (j : K ↪ K') (ι' : K' → Type*) {P' : Ideal (MRing ι' F)}
    (hP' : IsMultiHomogIdeal P') (T : Finset K) (q : MRing (fun k => ι' (j k)) F)
    (hq : q ∈ contractPrime j P') : killBlocks T q ∈ contractPrime j P' := by
  change rename (blockIncl j ι') (killBlocks T q) ∈ P'
  rw [rename_killBlocks]
  exact killBlocks_mem_of_isMultiHomogIdeal hP' _ hq
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
