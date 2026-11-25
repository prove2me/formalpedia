-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.norm_jj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:08:12.646864+00:00
-- url     : https://prove2.me/submissions/919aa41c-5c92-4026-b6cd-ba6b0682d8ef

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
theorem _root_.solution (t : EuclideanSpace ℂ (Fin (gB K))) : ‖jj K t‖ = ‖t‖ := by
  unfold jj
  rw [show ‖(((ob2 K).repr.symm t : V2 K) : EuclideanSpace ℂ ι)‖ = ‖(ob2 K).repr.symm t‖ from rfl,
    LinearIsometryEquiv.norm_map]
end ReciprocityTheory.ChartRestriction.G.I2.Col
