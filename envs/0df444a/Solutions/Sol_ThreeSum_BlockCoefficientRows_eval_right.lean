-- Prove2me | solution 1 for ThreeSum.BlockCoefficientRows.eval_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:13.109602+00:00
-- url     : https://prove2.me/submissions/8fde88b2-9b25-4886-925f-5aa3e97425ee

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Theorems.Thm_ThreeSum_BlockCoefficientRows_flat_coefficient
import Definitions.Def_WeightedCache3SUM_Alias_0e0667f8ae00b861


set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds
namespace ThreeSum.BlockCoefficientRows
theorem _root_.solution {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointRight o S := by
  rw [flat_coefficient,flat_coefficient]
  exact maskHash_right o S
end ThreeSum.BlockCoefficientRows
