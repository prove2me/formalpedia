-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalTensorChannels.sum_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:55.819328+00:00
-- url     : https://prove2.me/submissions/c81b01ae-dad8-4810-8d8a-360d673f3231

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalTensorChannels
open Finset TernaryJointType TernaryWeightedPhysicalSources TernaryWeightChannels
open scoped BigOperators
variable {ι κ I : Type*}
namespace ThreeSum.TernaryPhysicalTensorChannels
theorem _root_.solution {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N) (Q : TritWord N) (F : ι×κ→ℤ) :
    (∑ x : records S T left right Q, F x.val)=
      ∑ i∈S, ∑ j∈T, if TernaryConvolution.Adds (left i) (right j) Q then F (i,j) else 0 := by
  classical
  rw [sum_coe_sort]
  unfold records
  rw [sum_filter,sum_product]
end ThreeSum.TernaryPhysicalTensorChannels
