-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_nearWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:17:54.514208+00:00
-- url     : https://prove2.me/submissions/f00cdfa5-5649-4a23-89f4-876ee21f2b9a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
theorem _root_.solution {N D : ℕ} {R Q : TritWord N} :
    R∈nearWords Q D ↔ Below R Q ∧ deficit Q R≤D := WeightedNearBankEnumeration.mem_nearWords
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
