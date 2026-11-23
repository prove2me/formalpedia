-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.uc_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:21.533179+00:00
-- url     : https://prove2.me/submissions/52fafe8d-0b8b-49b3-a96d-dcc153ed8fad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_add_l


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {E : Type} [Field E] [NumberField E]
variable (X : PT E) (I : Submodule ℤ (Vsp X.dim))
variable {X I}
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (x y : Vsp X.dim) : uc (IR I) (x + y) = uc (IR I) x + uc (IR I) y := by
  simp [uc, z, Hf_add_l, add_smul, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.I2.Col
