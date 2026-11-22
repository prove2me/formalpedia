-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:50.923859+00:00
-- url     : https://prove2.me/submissions/06eb8520-e10a-46c4-a0dc-8349b24e0245

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (β β' : Fin (N + 1 + 1) × Fin r →₀ ℕ) : δv (β + β') = δv β + δv β' := by
  funext i; simp [δv, sum_add_distrib]
end Formalism.GM.gammaIntegralityLemmas
