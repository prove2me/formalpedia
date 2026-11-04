-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalSources.histogram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:42.694385+00:00
-- url     : https://prove2.me/submissions/469a566f-104b-470a-a4ed-7a4d3483b8c0

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPhysicalSources
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryConvolution
variable {ι κ : Type*}
namespace ThreeSum.TernaryPhysicalSources
theorem _root_.solution {N : ℕ} (S : Finset ι) (word : ι → TritWord N) (A : TritWord N) :
    0 ≤ histogram S word A := by
  apply Finset.sum_nonneg
  intro i hi
  split <;> norm_num
end ThreeSum.TernaryPhysicalSources
