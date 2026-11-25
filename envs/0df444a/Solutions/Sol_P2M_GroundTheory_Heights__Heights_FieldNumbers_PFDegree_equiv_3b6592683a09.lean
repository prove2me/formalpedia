-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_equiv_3b6592683a09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:05.116503+00:00
-- url     : https://prove2.me/submissions/9c3cd3a5-83ff-4c84-a4cc-5fd384204556

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_toIndefiniteRowSideFullHecke_a42574d499b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_split_model_to_place_model_4baa9be73125

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
namespace PFDegree
theorem _root_.solution (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} ↔ IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} :=
  ⟨PFDegree.toIndefiniteRowSideFullHecke, PFDegree.split_model_to_place_model h₁ h₂ h₃ h₄⟩
end PFDegree
end GroundTheory.Heights₂.Heights.FieldNumbers
