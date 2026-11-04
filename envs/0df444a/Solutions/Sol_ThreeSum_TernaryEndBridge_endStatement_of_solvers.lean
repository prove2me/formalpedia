-- Prove2me | solution 1 for ThreeSum.TernaryEndBridge.endStatement_of_solvers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:08:58.504634+00:00
-- url     : https://prove2.me/submissions/bca3d21d-8836-45e2-ad7c-2477b28aaac4

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Theorems.Thm_ThreeSum_TernaryEndBridge_solvedAt_of_solves
import Definitions.Def_WeightedCache3SUM_Alias_a17d8b98f28df35e


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
          timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by
  have hall : ThreeSumApsp.WordRam.SolvedInTime EndStatement.ThreeSum (r : ℝ) 0 := by
    intro κ
    obtain ⟨P, p, T, need, hs, hp, ht⟩ := h κ
    exact solvedAt_of_solves hs hp ht
  exact hall.endStatement rfl hr
end ThreeSum.TernaryEndBridge
