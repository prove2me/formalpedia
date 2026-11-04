-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedSelectedChain.selected_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:16:31.821028+00:00
-- url     : https://prove2.me/submissions/06c23ce2-fdd1-481b-a9d3-76049bfaf8ec

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
import Theorems.Thm_ThreeSum_TernaryPairedRecurrence_paired_zero_of_initial_budget
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_lower
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_lower
import Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_collision_bound
import Theorems.Thm_ThreeSum_WeightedGlobalPairedNativeDrift_paired_native_drift


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedSelectedChain
open Filter Real Finset TernaryPairedRecurrence TernaryPairedInitial WeightedGlobalPairedNativeDrift
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalLocalParameters TernaryCoverLocal
open WeightedGlobalEntropyRates
open WeightedGlobalSignedPadding TernaryPairedPotential TernaryPairedSupportConcrete
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalPairedSelectedChain
theorem _root_.solution (K m n b : ℕ) (hk : 0<K) (hm : 0<m) (hn : 1<n)
    (hF : (9*(nativeFamily K m (selectedMoment K)).length)^4≤outputSize m)
    (hp9 : 9<nativePrime K m)
    (Pi B C : ℕ→ℕ)
    (hstepPi : ∀ j, nativePrime K m^(2*K)*Pi (j+1)≤
      (9*(nativeFamily K m (selectedMoment K)).length*outputSize m*partitionCap m^K)*Pi j)
    (hstepB : ∀ j, nativePrime K m*B (j+1)≤9*B j)
    (hstepC : ∀ j, nativePrime K m*C (j+1)≤9*C j)
    (hinit : (Pi 0)^4≤((2*K).factorial*b^(2*K))^8*n^(8*K+5))
    (hinitB : B 0≤n^2) (hinitC : C 0≤n^2)
    (hnlarge : ((2*K).factorial*b^(2*K))^8<n)
    (hrate : WeightedGlobalPairedCollisionRate.charge K m<(7483/10000 : ℝ)) :
    Pi (radixLength m n)=0 ∧
      (B (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) ∧
      (C (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by
  have hbudget := paired_native_drift K (outputSize m) (partitionCap m) (inflation K m)
    (nativePrime K m) (nativeFamily K m (selectedMoment K)).length (inflation_lower hk m)
    (nativePrime_lower K m) hF
  have hzero := paired_zero_of_initial_budget K (outputSize m) (nativePrime K m^(2*K))
    (9*(nativeFamily K m (selectedMoment K)).length*outputSize m*partitionCap m^K)
    n (((2*K).factorial*b^(2*K))^8) (pow_pos (nativePrime_prime K m).pos _) Pi hstepPi
    hbudget (radixLength m n)
    (Nat.le_pow_clog (by have := outputSize_ge_sixteen hm; omega) (n^2)) hinit hnlarge
  have hB := WeightedGlobalPairedCollisionRate.collision_bound hm hn hp9 B hstepB hinitB
  have hC := WeightedGlobalPairedCollisionRate.collision_bound hm hn hp9 C hstepC hinitC
  have hpow := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ)≤n by exact_mod_cast hn.le) hrate.le
  exact ⟨hzero,hB.trans hpow,hC.trans hpow⟩
end ThreeSum.WeightedGlobalPairedSelectedChain
