-- Prove2me | solution 1 for ThreeSum.WeightedGlobalComputedExtensionMenu.functional_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:54:22.554088+00:00
-- url     : https://prove2.me/submissions/d96d36a8-3457-4790-aa76-68349781c917

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_constantCoefficient_ne_zero


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalComputedExtensionMenu
open Polynomial TernaryExtensionEncoding LightExtensionBackendLayout
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
variable {d c : ℕ} [Fact (Irreducible (modulus p d c))]
namespace ThreeSum.WeightedGlobalComputedExtensionMenu
theorem _root_.solution (hd : 0<d) : (functional (p:=p) (c:=c) hd)≠0 :=
  constantCoefficient_ne_zero (monic (p:=p) d c) _
end ThreeSum.WeightedGlobalComputedExtensionMenu
