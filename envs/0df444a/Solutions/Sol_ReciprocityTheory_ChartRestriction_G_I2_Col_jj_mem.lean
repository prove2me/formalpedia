-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.jj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:45.494882+00:00
-- url     : https://prove2.me/submissions/a616139c-1b8f-4882-a014-0011a13fe44c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
variable (K : Submodule ℝ (EuclideanSpace ℂ ι))
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (t : EuclideanSpace ℂ (Fin (gB K))) : jj K t ∈ V2 K := ((ob2 K).repr.symm t).2
end ReciprocityTheory.ChartRestriction.G.I2.Col
