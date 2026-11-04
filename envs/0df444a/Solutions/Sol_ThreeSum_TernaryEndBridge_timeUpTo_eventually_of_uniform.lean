-- Prove2me | solution 1 for ThreeSum.TernaryEndBridge.timeUpTo_eventually_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:30.214165+00:00
-- url     : https://prove2.me/submissions/528e1ddf-d939-4a2e-94b2-379714d88703

import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ThreeSumLayout
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Theorems.Thm_Light_timeUpTo_le
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEndBridge
open Light
noncomputable section
namespace ThreeSum.TernaryEndBridge
theorem _root_.solution {κ : ℕ} {T : ℕ → ℕ → ℕ} {a : ℝ}
    (ht : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ U : ℕ, U ≤ n ^ κ → (T n U : ℝ) ≤ (n : ℝ) ^ a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      timeUpTo T n ((n : ℝ) ^ (κ : ℝ)) ≤ (n : ℝ) ^ a := by
  filter_upwards [ht] with n hn
  apply timeUpTo_le
  intro U hU
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) ^ (κ : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcast : (U : ℝ) ≤ (n : ℝ) ^ (κ : ℝ) :=
    hU.trans (max_le le_rfl hnonneg)
  rw [Real.rpow_natCast] at hcast
  have hnat : U ≤ n ^ κ := by exact_mod_cast hcast
  exact hn U hnat
end ThreeSum.TernaryEndBridge
