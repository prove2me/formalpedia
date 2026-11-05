-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu.functional_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:25:48.761125+00:00
-- url     : https://prove2.me/submissions/0ec8e4da-1743-4ef6-ae61-5cc22fff8ac3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_constantCoefficient_ne_zero


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu
open Polynomial TernaryExtensionEncoding LightExtensionBackendLayout
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
variable {d c : ℕ} [Fact (Irreducible (modulus p d c))]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu
theorem _root_.solution (hd : 0<d) : (functional (p:=p) (c:=c) hd)≠0 :=
  constantCoefficient_ne_zero (monic (p:=p) d c) _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu
