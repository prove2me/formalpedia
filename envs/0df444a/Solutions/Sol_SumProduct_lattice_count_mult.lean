-- Prove2me | solution 1 for SumProduct.lattice_count_mult
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:38:41.617227+00:00
-- url     : https://prove2.me/submissions/00866a7c-5fbb-475e-a9be-99275ebf8030

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
import Theorems.Thm_SumProduct_boxMult_card_ge
import Theorems.Thm_SumProduct_boxMult_card_le

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    Y ^ (d - 1) / (Real.sqrt d * NumberField.Units.regulator K) ≤ (boxMult K Y).card ∧
      ((boxMult K Y).card : ℝ) ≤ 10 * (5 * Y + 1) ^ (d - 1) :=
  ⟨boxMult_card_ge d hd Y hY, boxMult_card_le hd Y hY⟩
end SumProduct
