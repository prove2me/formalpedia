-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPolynomial.tensorIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:45:38.608618+00:00
-- url     : https://prove2.me/submissions/d9d27f26-d406-4373-b1de-0b8fd1be37df

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPolynomial
theorem _root_.solution {Λ a b c d : ℕ} (ha : a<Λ) (hb : b<Λ) (hc : c<Λ) (hd : d<Λ) :
    tensorIndex Λ a b c d < Λ^4 := by
  have h₁ : a*Λ+b < Λ^2 := by nlinarith
  have h₂ : (a*Λ+b)*Λ+c < Λ^3 := by nlinarith [Nat.zero_le Λ]
  unfold tensorIndex
  nlinarith [Nat.zero_le Λ]
end ThreeSum.LightTernaryPairedPolynomial
