-- Prove2me | solution 1 for ThreeSum.WantedResidueKeys.code_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:09.037193+00:00
-- url     : https://prove2.me/submissions/0b197f44-7df5-4f14-9a97-63ff45491614

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Theorems.Thm_ThreeSum_WantedResidueKeys_code_eq_residue
import Theorems.Thm_ThreeSum_LightResidueHistogram_residue_eq_iff
import Theorems.Thm_ThreeSum_WantedPairs_residue_eq_iff


set_option autoImplicit false
open ThreeSum ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators
namespace ThreeSum.WantedResidueKeys
theorem _root_.solution {M : ℕ} (hM : 0 < M) (a b shift : ℤ) :
    code M 0 b=code M shift a ↔ (M : ℤ) ∣ a+shift-b := by
  rw [code_eq_residue,code_eq_residue,add_zero]
  exact WantedPairs.residue_eq_iff hM a b shift
end ThreeSum.WantedResidueKeys
