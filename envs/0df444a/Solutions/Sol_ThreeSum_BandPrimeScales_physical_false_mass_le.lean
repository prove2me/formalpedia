-- Prove2me | solution 1 for ThreeSum.BandPrimeScales.physical_false_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:35.267126+00:00
-- url     : https://prove2.me/submissions/bd7860c8-3987-471a-9f7f-c2febe089630

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Theorems.Thm_ThreeSum_BandPrimeScales_physicalMass_eq_score
import Theorems.Thm_ThreeSum_BandPrimeScales_modulus_loss
import Theorems.Thm_ThreeSum_BandPrimeScales_initial_score_bound
import Theorems.Thm_ThreeSum_BandPrimeScales_score_loss
import Theorems.Thm_ThreeSum_MassScales_false_mass_le


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.BandPrimeScales
theorem _root_.solution {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hcount : rs.length ≤ 3*bandCount n^2)
    (hbudget : divisorBudget k n*primeWindow n ≤
      candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    (physicalMass n (modulus n nA nB nC A B C rs) nA nB nC A B C rs : ℝ) ≤
      MassScales.falseMajorant k n := by
  rw [physicalMass_eq_score]
  exact MassScales.false_mass_le (score_loss A B C rs hbudget hA hB hC)
    (initial_score_bound A B C rs hcount) (modulus_loss n nA nB nC A B C rs)
end ThreeSum.BandPrimeScales
