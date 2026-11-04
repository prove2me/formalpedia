-- Prove2me | solution 1 for ThreeSum.WantedResidueKeys.selected_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:50.284355+00:00
-- url     : https://prove2.me/submissions/454790c2-157a-4999-ad7a-b8ca07d7da21

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Theorems.Thm_ThreeSum_ModuloCounts_signedHistogram_congr


set_option autoImplicit false
open ThreeSum ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators
namespace ThreeSum.WantedResidueKeys
theorem _root_.solution {M NL NR : ℕ} [NeZero M] {left left' right right' : ℕ → ℤ}
    (hleft : ∀ i < NL, left i=left' i) (hright : ∀ i < NR, right i=right' i) :
    LightOriginalOffset.selected M left right NL NR=
      LightOriginalOffset.selected M left' right' NL NR := by
  unfold LightOriginalOffset.selected
  rw [ModuloCounts.signedHistogram_congr (p := M) (c := 1) hleft,
    ModuloCounts.signedHistogram_congr (p := M) (c := 1) hright]
end ThreeSum.WantedResidueKeys
