-- Prove2me | solution 1 for ThreeSum.TernaryWeightedPhysicalSources.histogram_type_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:30.595945+00:00
-- url     : https://prove2.me/submissions/cb6d4462-e63a-4456-9d4d-e17f05193570

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_histogram_homogeneous
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_histogram_homogeneous
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_rank_of_type


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWeightedPhysicalSources
open Finset TernaryJointType TernaryBank TernaryConvolution
open scoped BigOperators
variable {ι κ : Type*}
namespace ThreeSum.TernaryWeightedPhysicalSources
theorem _root_.solution {N : ℕ} (S : Finset ι)
    (word : ι → TritWord N) (weight : ι → ℤ) (α : DigitType)
    (htype : ∀ i ∈ S, HasType (word i) α) :
    ∀ A, histogram S word weight A≠0 → rank A=α 1+2*α 2 :=
  histogram_homogeneous S word weight
    (fun i hi => TernaryPhysicalSources.rank_of_type (htype i hi))
end ThreeSum.TernaryWeightedPhysicalSources
