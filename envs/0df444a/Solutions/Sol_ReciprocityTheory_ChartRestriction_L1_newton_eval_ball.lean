-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.newton_eval_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:39:16.515097+00:00
-- url     : https://prove2.me/submissions/703d877d-50c6-45de-be55-1e30f25b72d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (Q : Polynomial (newtonBall K)) (a : newtonBall K) :
    (Q.map (newtonBall K).subtype).eval (a : K) = ((Q.eval a : newtonBall K) : K) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (newtonBall K).subtype a
end ReciprocityTheory.ChartRestriction.L1
