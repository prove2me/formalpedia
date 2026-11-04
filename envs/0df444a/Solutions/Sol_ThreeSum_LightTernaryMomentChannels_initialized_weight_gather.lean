-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentChannels.initialized_weight_gather
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:03.467038+00:00
-- url     : https://prove2.me/submissions/1a61c5db-11e0-4f79-8265-765c3765c7ca

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentChannels
theorem _root_.solution {μ : ℕ→ℤ} {dst originalCount count : ℕ}
    (weight : ℕ→ℤ) (originalPosition : ℕ→ℕ)
    (hinit : ∀ i<originalCount, μ (dst+i)=weight i)
    (hpos : ∀ i<count, originalPosition i<originalCount) :
    ∀ i<count, μ (dst+originalPosition i)=weight (originalPosition i) := by
  intro i hi
  exact hinit _ (hpos i hi)
end ThreeSum.LightTernaryMomentChannels
