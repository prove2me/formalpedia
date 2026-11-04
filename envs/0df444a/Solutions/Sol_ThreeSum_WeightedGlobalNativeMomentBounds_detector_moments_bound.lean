-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativeMomentBounds.detector_moments_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:03:06.562005+00:00
-- url     : https://prove2.me/submissions/6ed85e58-94a3-4f7a-a2ba-8b424b8c8426

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_moment_abs_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators
namespace ThreeSum.WeightedGlobalNativeMomentBounds
theorem _root_.solution {N U H : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (hB : ∀ j<S.left.NL, |B j|≤(U : ℤ))
    (hC : ∀ j<S.right.NL, |C j|≤(U : ℤ)) :
    ∀ i, ∀ k≤2*H, |∑ p : Pair S i, mass S i p*mode B C p^k|≤(detectorInput S U H : ℤ) := by
  intro i k hk
  exact (moment_abs_le S B C i hk hB hC).trans (by unfold detectorInput; push_cast; omega)
end ThreeSum.WeightedGlobalNativeMomentBounds
