-- Prove2me | solution 1 for ThreeSum.BandPrimeScales.modulus_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:23.036285+00:00
-- url     : https://prove2.me/submissions/cb237245-dab7-4ea1-ab07-6c212ff60fc8

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Theorems.Thm_ThreeSum_BandPrimeScales_modulus_bounds
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds
import Definitions.Def_WeightedCache3SUM_Alias_9e4cafb1427c81bb


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.BandPrimeScales
theorem _root_.solution (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    radix n ≤ primeLoss radix n*modulus n nA nB nC A B C rs :=
  primeDepth_loss_bound radix (modulus_bounds n nA nB nC A B C rs).1
end ThreeSum.BandPrimeScales
