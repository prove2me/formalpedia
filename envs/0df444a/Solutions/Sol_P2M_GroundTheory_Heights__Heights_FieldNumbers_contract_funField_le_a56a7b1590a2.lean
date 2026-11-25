-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_contract_funField_le_a56a7b1590a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:13.106314+00:00
-- url     : https://prove2.me/submissions/ec65dd59-6646-42cd-9895-137c36b639a7

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (h₁ : RenameMultiHomog.Statement.{u}) {F : Type u} [Field F]
    {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type}
    (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
  refine IntermediateField.subset_adjoin _ _ ⟨Function.extend j d 0, rename (blockIncl j ι') f,
    rename (blockIncl j ι') g, h₁ F K K' j _ ι' _ (fun _ => rfl) f d hf,
    h₁ F K K' j _ ι' _ (fun _ => rfl) g d hg, hgP, ?_⟩
  simp [contractFracMap, contractQuot, map_div₀]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
