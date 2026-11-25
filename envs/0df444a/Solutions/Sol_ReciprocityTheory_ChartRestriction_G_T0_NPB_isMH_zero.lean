-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.isMH_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:41.69618+00:00
-- url     : https://prove2.me/submissions/5f68e7a3-3ee0-4d38-a4dc-cabdf468fcce

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {R : Type*} [CommSemiring R] {B n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs
end ReciprocityTheory.ChartRestriction.G.T0.NPB
