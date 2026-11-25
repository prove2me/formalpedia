-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_split_8ca83a496a75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:00.565797+00:00
-- url     : https://prove2.me/submissions/5b937b1b-142a-4958-a499-7656dbd3786a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime

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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (b : K → ℤ) :
    IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) b ∘ (splitBlockEquiv j).symm = pullDeg j b := by
  funext k'
  obtain ⟨s, rfl⟩ := (splitBlockEquiv j).surjective k'
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rcases s with k | l
  · exact (j.injective.extend_apply b 0 k).symm
  · show (0 : ℤ) = Function.extend j b 0 l.1
    rw [Function.extend_apply' _ _ _ (fun h => l.2 h)]
    rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
