-- Prove2me | solution 1 for ThreeSum.TernaryHybridResources.power_word_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:55.927774+00:00
-- url     : https://prove2.me/submissions/5a945e16-8a48-4c65-880f-5b1e2fc16cc8

import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Theorems.Thm_ThreeSum_TernaryHybridResources_scalar_word_of_ok

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridResources
open Light StageBounds ArithmeticStageBounds
set_option maxHeartbeats 1700000
set_option maxRecDepth 16000
variable (fastNeed : ℕ → ℕ → Light.Need)
namespace ThreeSum.TernaryHybridResources
theorem _root_.solution {lim : Limits} {κ cutoff n U free d i : ℕ}
    (H : (need fastNeed κ cutoff n U).Ok lim free d) (hi : i≤κ) : ((n^i : ℕ) : ℤ)≤lim.word := by
  have hh : n^i≤(n+1)^(κ+1) :=
    (Nat.pow_le_pow_left (by omega : n≤n+1) i).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  exact (Int.ofNat_le.mpr (show n^i≤n+κ+cutoff+U+(n+1)^(κ+1)+10 by omega)).trans
    (scalar_word_of_ok fastNeed H)
end ThreeSum.TernaryHybridResources
