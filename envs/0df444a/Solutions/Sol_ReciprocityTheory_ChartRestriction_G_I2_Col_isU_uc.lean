-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.isU_uc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:48.804241+00:00
-- url     : https://prove2.me/submissions/d61bae24-a4ad-4acf-9db8-0f8730a116a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_inner_uc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_uc_mem


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
theorem _root_.solution (x : Vsp X.dim) : IsU I x (uc (IR I) x) :=
  ⟨uc_mem _ x, fun a ha => inner_uc _ x a ha⟩
end ReciprocityTheory.ChartRestriction.G.I2.Col
