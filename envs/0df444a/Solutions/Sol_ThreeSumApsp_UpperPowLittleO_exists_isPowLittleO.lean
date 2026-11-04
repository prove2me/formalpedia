-- Prove2me | solution 1 for ThreeSumApsp.UpperPowLittleO.exists_isPowLittleO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:18.044548+00:00
-- url     : https://prove2.me/submissions/1482dd63-f71d-4752-9683-4e1ffe17cb9c

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowLittleO
namespace ThreeSumApsp.UpperPowLittleO
theorem _root_.solution (h : UpperPowLittleO f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowLittleO g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by
  obtain ⟨ε, hε, hf⟩ := h
  exact ⟨fun n => (n : ℝ) ^ (a + ε n), fun n => Real.rpow_nonneg n.cast_nonneg _,
    ⟨ε, hε, Eventually.of_forall fun n => (abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg _)).le⟩,
    hf⟩
end ThreeSumApsp.UpperPowLittleO
