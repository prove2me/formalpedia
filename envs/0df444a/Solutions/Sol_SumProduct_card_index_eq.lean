-- Prove2me | solution 1 for SumProduct.card_index_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:52:14.384844+00:00
-- url     : https://prove2.me/submissions/9bc77573-c301-4364-9e62-851dcba7451f

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
open scoped Classical
open NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) :
    Fintype.card {w : InfinitePlace K // w ≠ w₀} = d - 1 := by
  classical
  have hcard : Fintype.card (InfinitePlace K) = d := by
    have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
    have hc := card_eq_nrRealPlaces_add_nrComplexPlaces K
    have hr := card_add_two_mul_card_eq_rank K
    rw [hd] at hr; omega
  rw [← hcard]
  exact Set.card_ne_eq w₀
end SumProduct
