-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.uc_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:10.411548+00:00
-- url     : https://prove2.me/submissions/89e06db5-912c-4546-8f12-a64c83d4d53a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_e_mem

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
theorem _root_.solution (v : EuclideanSpace ℂ ι) : uc K v ∈ K := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (e_mem K k)
end ReciprocityTheory.ChartRestriction.G.I2.Col
