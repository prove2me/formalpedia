-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.coord_of_mem_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:36.523874+00:00
-- url     : https://prove2.me/submissions/6ff057b2-2166-4fb3-9af7-b738f0ed4bf6

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
theorem _root_.solution {v : EuclideanSpace ℂ ι} (hv : v ∈ V2 K) (k : Fin (dK K)) : z K k v = 0 := by
  rw [z, Hf_eq_inner]
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self k) : e K k ∈ span1 K) hv
end ReciprocityTheory.ChartRestriction.G.I2.Col
