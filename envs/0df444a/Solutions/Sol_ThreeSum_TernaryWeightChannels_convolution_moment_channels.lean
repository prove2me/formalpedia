-- Prove2me | solution 1 for ThreeSum.TernaryWeightChannels.convolution_moment_channels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:09.11245+00:00
-- url     : https://prove2.me/submissions/228bb6c8-f5ab-484c-b107-a4a3b4500985

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Theorems.Thm_ThreeSum_TernaryWeightChannels_pair_moment_channels
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_convolution_histograms
import Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_convolution_histograms


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators
variable {ι κ I : Type*}
namespace ThreeSum.TernaryWeightChannels
theorem _root_.solution {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : TritWord N) (k : ℕ) :
    (∑ j∈range (k+1), TernaryConvolution.convolution
      (histogram S left (fun i => (leftMoment k j).eval (fun _ => B i)))
      (histogram T right (fun i => (rightMoment k j).eval (fun _ => C i))) Q)=
      ∑ b∈S, ∑ c∈T, if TernaryConvolution.Adds (left b) (right c) Q then
        (C c-B b)^k else 0 := by
  simp_rw [convolution_histograms]
  exact pair_moment_channels S T left right B C Q k
end ThreeSum.TernaryWeightChannels
