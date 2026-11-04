-- Prove2me | solution 1 for ThreeSum.TernaryEndBridge.endStatement_of_uniform_solvers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:12:41.214614+00:00
-- url     : https://prove2.me/submissions/550088f3-c1ef-4ea9-b28c-f8599201092a

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Theorems.Thm_ThreeSum_TernaryEndBridge_timeUpTo_eventually_of_uniform
import Theorems.Thm_ThreeSum_TernaryEndBridge_endStatement_of_solvers

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEndBridge
open Light
noncomputable section
namespace ThreeSum.TernaryEndBridge
theorem _root_.solution {r : ℚ} (hr : 0 ≤ r)
    (h : ∀ κ : ℕ,
      ∃ (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need),
        Solves s3Task P p T need ∧ PolyNeed need ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ U : ℕ, U ≤ n ^ κ → (T n U : ℝ) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by
  apply endStatement_of_solvers hr
  intro κ
  obtain ⟨P, p, T, need, hs, hp, ht⟩ := h κ
  exact ⟨P, p, T, need, hs, hp, timeUpTo_eventually_of_uniform ht⟩
end ThreeSum.TernaryEndBridge
