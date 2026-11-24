-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas_zpow_mono__fc2d0d98fdd7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:23.951059+00:00
-- url     : https://prove2.me/submissions/03c2437c-28d7-41c8-936f-15571fe71f56

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_p_real_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution {a b : ℤ} (h : a ≤ b) : (p : ℝ) ^ a ≤ (p : ℝ) ^ b :=
  zpow_le_zpow_right₀ p_real_one_le h
end Formalism.GM.gammaIntegralityLemmas
