-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSelectedSigned.native_signed_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:42:53.903335+00:00
-- url     : https://prove2.me/submissions/36b76c0e-86e9-4675-b67a-1e972913c5e4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_input_eq
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedTerminal_native_zero


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSelectedSigned
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs)
    (K n U0 r U radix nA M C0 : ℕ) (s : State (p := p) A) (X B C : ℕ→ℤ)
    (hbudget : Budget maps τ cap Q (base I A.J nA) A K n U0
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) r s)
    (hb : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hinit : U0^4≤C0*n^(8*K+5)) (hn : C0<n) :
    WeightedGlobalNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q
        (WeightedGlobalArenaNativeComplete.input I U radix nA (selectedHash A s r) X B C)) K A.J
      (fun j i => feature (leftRaw U radix A.J (B j)) i)
      (fun j i => feature (rightRaw U radix A.J (C j)) i)=0 := by
  have hz := native_zero maps τ cap Q (base I A.J nA) A K n U0
    (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) r s M C0
    hbudget hb hdrift hcover hinit hn
  rw [input_eq] at hz
  exact hz
end ThreeSum.WeightedGlobalArenaSelectedSigned
