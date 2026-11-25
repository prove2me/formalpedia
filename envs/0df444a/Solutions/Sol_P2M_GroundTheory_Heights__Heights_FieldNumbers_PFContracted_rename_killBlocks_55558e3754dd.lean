-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_killBlocks_55558e3754dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:42.317701+00:00
-- url     : https://prove2.me/submissions/c87871a4-2140-4a67-8266-a7092386ab4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution (j : K ↪ K') (ι' : K' → Type*) (T : Finset K)
    (q : MRing (fun k => ι' (j k)) F) :
    rename (blockIncl j ι') (killBlocks T q) = killBlocks (T.map j) (rename (blockIncl j ι') q) := by
  have : (rename (blockIncl j ι')).comp (killBlocks (F := F) T) =
      (killBlocks (T.map j)).comp (rename (blockIncl j ι')) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X, killBlocks_X, blockIncl, Finset.mem_map',
      apply_ite (rename (blockIncl j ι')), map_zero]
  exact AlgHom.congr_fun this q
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
