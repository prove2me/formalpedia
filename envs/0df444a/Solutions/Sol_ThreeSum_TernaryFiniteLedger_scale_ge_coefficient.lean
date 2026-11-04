-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.scale_ge_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:46.762201+00:00
-- url     : https://prove2.me/submissions/f62ab415-9648-4af7-8e91-2e726e697606

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution (C c d : ℕ) : c ≤ scale C c d := by
  have hc : c ≤ scaleAux C c d := by unfold scaleAux; omega
  have ht : scaleAux C c d ≤ 2*scaleAux C c d := by omega
  have hp : 2*scaleAux C c d ≤ 2^(2*scaleAux C c d) :=
    (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  exact hc.trans (ht.trans hp)
end ThreeSum.TernaryFiniteLedger
