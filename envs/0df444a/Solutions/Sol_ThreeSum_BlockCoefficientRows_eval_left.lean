-- Prove2me | solution 1 for ThreeSum.BlockCoefficientRows.eval_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:11.893062+00:00
-- url     : https://prove2.me/submissions/dd542f23-bac2-479f-94c5-c7559109c6f4

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Theorems.Thm_ThreeSum_BlockCoefficientRows_flat_coefficient
import Definitions.Def_WeightedCache3SUM_Alias_66a6a809f0c02273


set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds
namespace ThreeSum.BlockCoefficientRows
theorem _root_.solution {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointLeft o S := by
  rw [flat_coefficient,flat_coefficient]
  exact maskHash_left o S
end ThreeSum.BlockCoefficientRows
