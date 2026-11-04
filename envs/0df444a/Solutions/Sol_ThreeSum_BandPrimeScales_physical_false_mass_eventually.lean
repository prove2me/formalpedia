-- Prove2me | solution 1 for ThreeSum.BandPrimeScales.physical_false_mass_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:14.300197+00:00
-- url     : https://prove2.me/submissions/e2450835-acfb-4488-a076-973f5468f170

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Theorems.Thm_ThreeSum_BandPrimeScales_physical_false_mass_le
import Theorems.Thm_ThreeSum_Scales_actual_divisor_budget


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.BandPrimeScales
theorem _root_.solution (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record),
      rs.length ≤ 3*bandCount n^2 →
      (∀ i < nA, |A i| ≤ (n^k : ℤ)) →
      (∀ i < nB, |B i| ≤ (n^k : ℤ)) →
      (∀ i < nC, |C i| ≤ (n^k : ℤ)) →
      (physicalMass n (modulus n nA nB nC A B C rs) nA nB nC A B C rs : ℝ) ≤
        MassScales.falseMajorant k n := by
  filter_upwards [actual_divisor_budget k] with n hbudget
  intro nA nB nC A B C rs hcount hA hB hC
  exact physical_false_mass_le A B C rs hcount hbudget hA hB hC
end ThreeSum.BandPrimeScales
