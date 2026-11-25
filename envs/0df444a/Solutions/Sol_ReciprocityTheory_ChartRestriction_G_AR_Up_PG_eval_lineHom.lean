-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PG.eval_lineHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:34.248214+00:00
-- url     : https://prove2.me/submissions/e24b6746-6fe8-47dc-96fc-ae09656d7c0c

import Mathlib
import Definitions.Def_Lemmata_CofiniteContinuousBounds_LeOfCofinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PG
open MvPolynomial
variable {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PG
theorem _root_.solution (a w : Fin D → ℂ) (F : MvPolynomial (Fin D) ℂ) (s : ℂ) :
    (lineHom a w F).eval s = eval (fun i => a i + w i * s) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [lineHom]
  | add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    simp [lineHom]
end ReciprocityTheory.ChartRestriction.G.AR.Up.PG
