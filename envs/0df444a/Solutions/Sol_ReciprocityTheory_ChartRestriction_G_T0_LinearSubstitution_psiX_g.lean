-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.psiX_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:33.14562+00:00
-- url     : https://prove2.me/submissions/1a3a85c6-bc09-4fdf-bf31-b9363dae3f84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
theorem _root_.solution (t : TVar D N) :
    WH.psiP isX (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by
  simp [WH.psiP, gImg, isX]
  try ring
end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
