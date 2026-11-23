-- Prove2me | solution 1 for SumProduct.card_mul_self_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:15.614965+00:00
-- url     : https://prove2.me/submissions/596abf10-51ef-4caf-b9ba-7c07287e55f2

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {α : Type*} [CommMonoid α] [DecidableEq α] (S T : Finset α) :
    ((S * T) * (S * T)).card ≤ (S * S).card * (T * T).card := by
  rw [mul_mul_mul_comm]
  exact Finset.card_mul_le
end SumProduct
