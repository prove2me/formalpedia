-- Prove2me | solution 1 for ThreeSum.LightTernaryWantedBudget.node_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:16.423491+00:00
-- url     : https://prove2.me/submissions/e7592f50-2627-4ffb-a7da-8dae20537049

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedBudget
open LightTernaryWantedCanonical
namespace ThreeSum.LightTernaryWantedBudget
theorem _root_.solution (P V W : ℕ) (hV : V ≤ 2^W) :
    overhead P V+stepCost V+40 ≤ 1000*(P+W+3) := by
  have hp : 1 ≤ 2^W := one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))
  have hbound : 2*V+1 ≤ 2^(W+2) := by rw [pow_add]; norm_num; omega
  have hlog := Nat.log_mono_right (b := 2) hbound
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] at hlog
  unfold overhead stepCost LightResidues.residueBudget LightTernaryDivide.time LightOutputDecodeDivide.budget
  omega
end ThreeSum.LightTernaryWantedBudget
