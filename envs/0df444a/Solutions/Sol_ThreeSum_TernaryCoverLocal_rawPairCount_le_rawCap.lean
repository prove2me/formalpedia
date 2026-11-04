-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.rawPairCount_le_rawCap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:56:44.235196+00:00
-- url     : https://prove2.me/submissions/9962446e-d735-4a30-8f0c-21dcbcee4e62

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution (α π : DigitType)
    (w : Coordinate (Fin L) → ZMod p) (a b : ZMod p) :
    TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) a b ≤
      rawCap α π w := by
  classical
  unfold rawCap
  exact Finset.le_sup (f := fun t : ZMod p × ZMod p =>
    TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) t.1 t.2)
    (mem_univ (a,b))
end ThreeSum.TernaryCoverLocal
