-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.histogram_type_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:30.561276+00:00
-- url     : https://prove2.me/submissions/bfdd1544-de67-42b5-b158-1ec85c799d1b

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_rank_of_type
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_histogram_homogeneous

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution
variable {ι κ : Type*}
namespace ThreeSum.TernaryPhysicalSources
theorem _root_.solution {N : ℕ} (S : Finset ι)
    (word : ι → TritWord N) (α : DigitType)
    (htype : ∀ i ∈ S, HasType (word i) α) :
    ∀ A, histogram S word A≠0 → rank A=α 1+2*α 2 :=
  histogram_homogeneous S word (fun i hi => rank_of_type (htype i hi))
end ThreeSum.TernaryPhysicalSources
