-- Prove2me | solution 1 for ThreeSumApsp.eventually_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:51.556249+00:00
-- url     : https://prove2.me/submissions/3683368c-efd3-47e5-8a0c-be8e69b8b477

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution (c : ℝ) {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ η :=
  ((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c
end ThreeSumApsp
