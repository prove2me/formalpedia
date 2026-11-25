-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_proof_c7e248874611
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:15.031186+00:00
-- url     : https://prove2.me/submissions/7156db4d-a886-40c5-a5cc-cdaa4a7276ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_killStable_2361f4b4da88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_isRelevant_e828c0104b5a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_key_d10b44fcabab
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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace PFContracted
theorem _root_.solution (h1 : MixedDiffConst.Statement.{u}) (h2 : CutRational.Statement.{u}) :
    ProjectionFormulaContracted.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hrel hlt bs
  have := hP'.isPrime
  obtain ⟨D, -, hD⟩ := PFContracted.exists_ringKrullDim_eq
    (fun T q hq => PFContracted.killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq)
    hP'.relevant
  obtain ⟨D0, -, hD0⟩ := PFContracted.exists_ringKrullDim_eq
    (PFContracted.contractPrime_killStable j ι' hP'.multiHomog)
    (PFContracted.contractPrime_isRelevant j ι' hP'.relevant)
  rw [PFContracted.relDim_eq_int hD, PFContracted.natCast_withBot_withTop] at hrel
  rw [PFContracted.relDim_eq_int hD0, PFContracted.natCast_withBot_withTop] at hlt
  have e1 : (D : ℤ) - Fintype.card K' = n := WithTop.coe_inj.mp (WithBot.coe_inj.mp hrel)
  have e2 : (D0 : ℤ) - Fintype.card K < n := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hlt)
  exact PFContracted.key h1 h2 n P' hP' D D0 hD (by omega) hD0 (by omega) bs
end PFContracted
end GroundTheory.Heights₂.Heights.FieldNumbers
