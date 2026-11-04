-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalTensorChannels.fourth_tensor_on_physical_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:55.488268+00:00
-- url     : https://prove2.me/submissions/6d0c484f-1f1d-479a-9312-68b2defcd48d

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
import Theorems.Thm_ThreeSum_TernaryPhysicalTensorChannels_sum_records
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_convolution_histograms
import Theorems.Thm_ThreeSum_TernaryWeightChannels_fourth_pair_channel
import Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_convolution_histograms


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalTensorChannels
open Finset TernaryJointType TernaryWeightedPhysicalSources TernaryWeightChannels
open scoped BigOperators
variable {ι κ I : Type*}
namespace ThreeSum.TernaryPhysicalTensorChannels
theorem _root_.solution {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (L : ι→I→ℤ) (R : κ→I→ℤ) (a b c d : I) (Q : TritWord N) :
    TernaryConvolution.convolution
      (histogram S left (productWeight L a b))
      (histogram T right (productWeight R c d)) Q=
      TernaryPairedTensor.tensor (fun x : records S T left right Q => L x.val.1)
        (fun x : records S T left right Q => R x.val.2) a b c d := by
  rw [convolution_histograms,fourth_pair_channel]
  unfold TernaryPairedTensor.tensor
  exact (sum_records S T left right Q (fun x => L x.1 a*L x.1 b*R x.2 c*R x.2 d)).symm
end ThreeSum.TernaryPhysicalTensorChannels
