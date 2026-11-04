-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.scale_ge_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:53:52.778532+00:00
-- url     : https://prove2.me/submissions/200b93f9-e661-4e7d-892b-be6d2d5c7f81

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution (C c d : ℕ) : c ≤ scale C c d := by
  have hc : c ≤ scaleAux C c d := by unfold scaleAux; omega
  have ht : scaleAux C c d ≤ 2*scaleAux C c d := by omega
  have hp : 2*scaleAux C c d ≤ 2^(2*scaleAux C c d) :=
    (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  exact hc.trans (ht.trans hp)
end ThreeSum.WeightedGlobalFiniteLedger
