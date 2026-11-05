-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.cost_add_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:29.366468+00:00
-- url     : https://prove2.me/submissions/3f539659-d066-46cb-a557-b37830506244

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_concrete_cost_mono
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_cost_add_deficit


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
theorem _root_.solution {N : ℕ} {R Q : TritWord N} (h : Below R Q) :
    cacheCost R+deficit Q R=cacheCost Q :=
  WeightedCache.cost_add_deficit WeightedCache.concrete_cost_mono h
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
