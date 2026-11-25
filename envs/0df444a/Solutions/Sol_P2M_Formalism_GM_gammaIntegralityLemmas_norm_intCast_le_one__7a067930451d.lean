-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas_norm_intCast_le_one__7a067930451d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:14.34184+00:00
-- url     : https://prove2.me/submissions/548285a5-8560-455e-ac1c-2beb673d834d

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (n : ℤ) : ‖(n : ℚ_[p])‖ ≤ 1 :=
  Padic.norm_int_le_one n
end Formalism.GM.gammaIntegralityLemmas
