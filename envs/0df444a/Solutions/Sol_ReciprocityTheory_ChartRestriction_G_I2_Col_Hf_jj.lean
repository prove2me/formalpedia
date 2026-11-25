-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_jj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:26.49197+00:00
-- url     : https://prove2.me/submissions/2497a518-1d7e-4d6f-8f84-19f807b1b007

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_eq_inner

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
theorem _root_.solution (t t' : EuclideanSpace ℂ (Fin (gB K))) : Hf (jj K t) (jj K t') = Hf t t' := by
  rw [Hf_eq_inner, Hf_eq_inner, jj, jj, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
end ReciprocityTheory.ChartRestriction.G.I2.Col
