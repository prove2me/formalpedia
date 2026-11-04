-- Prove2me | solution 1 for ThreeSum.TernaryMomentSchedule.scaled_physical_moments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:30.380469+00:00
-- url     : https://prove2.me/submissions/00ff0e5b-9e91-47e3-8a03-e2b0fbf56d74

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_channel_rows
import Theorems.Thm_ThreeSum_TernaryWeightChannels_convolution_moment_channels


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators
namespace ThreeSum.TernaryMomentSchedule
theorem _root_.solution {ι κ : Type*} {N : ℕ}
    (S : Finset ι) (T : Finset κ) (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : ℕ→TritWord N) (scale : ℕ→ℤ)
    (terms k i : ℕ) (hk : k<terms) :
    aggregate (channels terms)
      (fun k j i => scale i*TernaryConvolution.convolution
        (TernaryWeightedPhysicalSources.histogram S left
          (fun b => (TernaryWeightChannels.leftMoment k j).eval (fun _ => B b)))
        (TernaryWeightedPhysicalSources.histogram T right
          (fun c => (TernaryWeightChannels.rightMoment k j).eval (fun _ => C c))) (Q i)) k i=
      scale i*∑ b∈S, ∑ c∈T,
        if TernaryConvolution.Adds (left b) (right c) (Q i) then (C c-B b)^k else 0 := by
  rw [channel_rows,if_pos hk,← mul_sum]
  exact congrArg (fun x : ℤ => scale i*x)
    (TernaryWeightChannels.convolution_moment_channels S T left right B C (Q i) k)
end ThreeSum.TernaryMomentSchedule
