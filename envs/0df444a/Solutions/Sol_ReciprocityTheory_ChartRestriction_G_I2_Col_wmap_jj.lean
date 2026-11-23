-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.wmap_jj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:45.976032+00:00
-- url     : https://prove2.me/submissions/3c9eac7a-87e5-4ead-825b-63438b27fab9

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
theorem _root_.solution (t : EuclideanSpace ℂ (Fin (gB K))) : wmap K (jj K t) = t := by
  unfold wmap jj
  simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
end ReciprocityTheory.ChartRestriction.G.I2.Col
