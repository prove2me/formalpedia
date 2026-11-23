-- Prove2me | solution 1 for SumProduct.card_construction_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:08:36.065707+00:00
-- url     : https://prove2.me/submissions/92a71931-9351-4271-840b-83378c3a3469

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
import Theorems.Thm_SumProduct_card_construction
import Theorems.Thm_SumProduct_floor_ratio_lt_goldenRatio


set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (Y : ℝ) {X ε : ℝ} (hX : 2 ≤ X) (hε0 : 0 < ε) (hε : ε ≤ 3 / 20) :
    ((boxMult K Y ×ˢ boxAdd K (ε * X)).image
        (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((⌊X⌋₊ : 𝓞 K) + gb.2))).card
      = (boxMult K Y).card * (boxAdd K (ε * X)).card := by
  refine card_construction (r := ε * X) ?_ (floor_ratio_lt_goldenRatio hX hε0 hε)
    (boxMult K Y) (boxAdd K (ε * X)) (fun b hb => hb)
  have hn2 : (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    exact_mod_cast Nat.le_floor (show ((2 : ℕ) : ℝ) ≤ X by exact_mod_cast hX)
  have hXlt : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  nlinarith [mul_le_mul_of_nonneg_right hε (show (0 : ℝ) ≤ X by linarith), hXlt, hn2]
end SumProduct
