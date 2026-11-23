-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas_zpow_pos__da61b7487fff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:45.564252+00:00
-- url     : https://prove2.me/submissions/17119897-320f-47cf-80a3-ddfd57764297

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
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (a : ℤ) : (0 : ℝ) < (p : ℝ) ^ a :=
  zpow_pos (by exact_mod_cast hp.out.pos) a
end Formalism.GM.gammaIntegralityLemmas
