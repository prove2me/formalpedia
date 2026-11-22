-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas_norm_natCast_le_one__a9d2d1dd10a2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:02.975371+00:00
-- url     : https://prove2.me/submissions/538b2eb6-8fac-4276-85ad-8c3710db2e4a

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
theorem _root_.solution (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := p) (n : ℤ)
  simpa using this
end Formalism.GM.gammaIntegralityLemmas
