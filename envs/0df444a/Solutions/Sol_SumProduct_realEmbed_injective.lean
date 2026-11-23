-- Prove2me | solution 1 for SumProduct.realEmbed_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:52.980201+00:00
-- url     : https://prove2.me/submissions/b425ae58-b132-44c2-903e-6745688995a4

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_exists_coord_dist_ge_one

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    Function.Injective (realEmbed K) := by
  intro α β h
  by_contra hne
  obtain ⟨w, hw⟩ := exists_coord_dist_ge_one hne
  rw [h, sub_self, abs_zero] at hw
  linarith
end SumProduct
