-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalTensorChannels.moment_on_physical_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:06.062281+00:00
-- url     : https://prove2.me/submissions/0ff79a28-6fc6-41fe-8873-ad0f00b7dd5d

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
import Theorems.Thm_ThreeSum_TernaryPhysicalTensorChannels_sum_records
import Theorems.Thm_ThreeSum_TernaryWeightChannels_convolution_moment_channels


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalTensorChannels
open Finset TernaryJointType TernaryWeightedPhysicalSources TernaryWeightChannels
open scoped BigOperators
variable {ι κ I : Type*}
namespace ThreeSum.TernaryPhysicalTensorChannels
theorem _root_.solution {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : TritWord N) (k : ℕ) :
    (∑ j∈range (k+1), TernaryConvolution.convolution
      (histogram S left (fun i => (leftMoment k j).eval (fun _ => B i)))
      (histogram T right (fun i => (rightMoment k j).eval (fun _ => C i))) Q)=
      ∑ x : records S T left right Q, (C x.val.2-B x.val.1)^k := by
  rw [convolution_moment_channels]
  exact (sum_records S T left right Q (fun x => (C x.2-B x.1)^k)).symm
end ThreeSum.TernaryPhysicalTensorChannels
