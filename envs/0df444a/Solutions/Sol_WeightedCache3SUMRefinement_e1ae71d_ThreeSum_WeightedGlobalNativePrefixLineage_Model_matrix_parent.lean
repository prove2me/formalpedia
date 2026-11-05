-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage.Model.matrix_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:27:58.641362+00:00
-- url     : https://prove2.me/submissions/e36b60bf-6bcc-4ccd-8a4e-ca0917b038fb

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairedLineage
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePrefixLineage

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p Λ L F : ℕ} [Fact p.Prime] {α π : DigitType}
variable {O B C : Type*} [Fintype O] [Fintype B] [Fintype C]
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage.Model
variable (M : Model p Λ L F α π O B C)
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage.Model
theorem _root_.solution {r K : ℕ} (x : M.Index (r+1) K) : M.matrix x=M.matrix (M.parent x) := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePrefixLineage.Model
