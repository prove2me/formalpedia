-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativePrefixLineage.Model.matrix_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:24:10.198395+00:00
-- url     : https://prove2.me/submissions/3a3e6c4a-cd2a-4fe8-acb9-e3ded3e78485

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairedLineage
import Definitions.Def_Submission_Weighted_Global_TernaryNativePrefixLineage

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePrefixLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p Λ L F : ℕ} [Fact p.Prime] {α π : DigitType}
variable {O B C : Type*} [Fintype O] [Fintype B] [Fintype C]
open ThreeSum.WeightedGlobalNativePrefixLineage.Model
variable (M : Model p Λ L F α π O B C)
namespace ThreeSum.WeightedGlobalNativePrefixLineage.Model
theorem _root_.solution {r K : ℕ} (x : M.Index (r+1) K) : M.matrix x=M.matrix (M.parent x) := rfl
end ThreeSum.WeightedGlobalNativePrefixLineage.Model
