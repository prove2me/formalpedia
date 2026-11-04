-- Prove2me | solution 1 for ThreeSum.BandPrimeScales.score_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:44.848843+00:00
-- url     : https://prove2.me/submissions/bf4eea68-a803-4516-832f-23f907a4a30a

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Theorems.Thm_ThreeSum_BandPrimeScales_modulus_bounds
import Theorems.Thm_ThreeSum_BandPrimeScales_score_contraction
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimePool_size_eq_card
import Theorems.Thm_ThreeSum_LightPrimePool_size_pos
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Definitions.Def_WeightedCache3SUM_Alias_6877b92cae24fac0


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.BandPrimeScales
theorem _root_.solution {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hbudget : divisorBudget k n*primeWindow n ≤
      candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    modulus n nA nB nC A B C rs*score n (modulus n nA nB nC A B C rs) nA nB nC A B C rs ≤
      scoreLoss k n*score n 1 nA nB nC A B C rs := by
  have hpos : 0 < (PrimeDensity.candidates (primeWindow n)).card := by
    rw [← LightPrimePool.size_eq_card]
    exact LightPrimePool.size_pos (by have := primeWindow_ge_two n; omega)
  exact scoreLoss_finite_bound hpos hbudget (score_contraction A B C rs hA hB hC)
    (modulus_bounds n nA nB nC A B C rs).2
end ThreeSum.BandPrimeScales
