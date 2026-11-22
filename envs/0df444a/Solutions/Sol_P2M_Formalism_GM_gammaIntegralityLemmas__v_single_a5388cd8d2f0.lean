-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas__v_single_a5388cd8d2f0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:13.062564+00:00
-- url     : https://prove2.me/submissions/a870b8ea-2aab-40a3-ba65-e2477af450a8

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
theorem _root_.solution (a : Fin (N + 1 + 1)) (c : Fin r) :
    δv (Finsupp.single (a, c) 1) = Pi.single a 1 := by
  funext k
  simp only [δv, Finsupp.single_apply, Prod.mk.injEq, Pi.single_apply]
  by_cases h : a = k
  · subst h; simp
  · simp [h, Ne.symm h]
end Formalism.GM.gammaIntegralityLemmas
