-- Prove2me | solution 1 for SumProduct.place_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:01:14.139765+00:00
-- url     : https://prove2.me/submissions/81aaf055-ccdc-41dc-9bc7-773ad71a9a9d

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
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (n : ℕ) : w (n : K) = n := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq w (n : K), map_natCast, Complex.norm_natCast]
end SumProduct
