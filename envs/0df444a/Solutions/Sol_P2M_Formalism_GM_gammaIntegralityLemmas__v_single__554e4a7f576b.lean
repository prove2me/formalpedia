-- Prove2me | solution 1 for P2M_Formalism_GM_gammaIntegralityLemmas__v_single__554e4a7f576b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:38.422803+00:00
-- url     : https://prove2.me/submissions/05b66d14-2483-4954-a2cd-3f846760538f

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
theorem _root_.solution (a : Fin (N + 1 + 1)) (c : Fin r) (t : ℕ) :
    δv (Finsupp.single (a, c) t) = Pi.single a t := by
  funext k
  simp only [δv, Finsupp.single_apply, Prod.mk.injEq, Pi.single_apply]
  by_cases h : a = k
  · subst h; simp
  · simp [h, Ne.symm h]
end Formalism.GM.gammaIntegralityLemmas
