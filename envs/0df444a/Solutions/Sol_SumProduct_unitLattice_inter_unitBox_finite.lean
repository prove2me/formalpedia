-- Prove2me | solution 1 for SumProduct.unitLattice_inter_unitBox_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:56:28.782632+00:00
-- url     : https://prove2.me/submissions/23f62afb-4262-42d6-8a07-1776861112c8

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Metric
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {Y : ℝ}
    (hY : 0 ≤ Y) : (↑(unitLattice K) ∩ unitBox K Y).Finite := by
  refine (unitLattice_inter_ball_finite K Y).subset ?_
  rintro x ⟨hx1, hx2, -⟩
  refine ⟨hx1, ?_⟩
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hY]
  intro w
  rw [Real.norm_eq_abs]
  exact hx2 w
end SumProduct
