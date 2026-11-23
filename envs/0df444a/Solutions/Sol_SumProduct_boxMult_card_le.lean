-- Prove2me | solution 1 for SumProduct.boxMult_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:36:34.202513+00:00
-- url     : https://prove2.me/submissions/fb982089-4ca5-4352-b081-f6f663a3bd69

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
import Theorems.Thm_SumProduct_boxMult_card_le_two_mul_image
import Theorems.Thm_SumProduct_unitLattice_inter_unitBox_packing
import Theorems.Thm_SumProduct_unitBox_inter_eq_image

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    ((boxMult K Y).card : ℝ) ≤ 10 * (5 * Y + 1) ^ (d - 1) := by
  have himgcard : ((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card
      = (↑(unitLattice K) ∩ unitBox K Y).ncard := by
    rw [← Set.ncard_coe_finset, unitBox_inter_eq_image]
  have h2 : ((boxMult K Y).card : ℝ)
      ≤ 2 * (((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card : ℝ) := by
    exact_mod_cast boxMult_card_le_two_mul_image
  have hpack := unitLattice_inter_unitBox_packing hd Y hY
  calc ((boxMult K Y).card : ℝ)
      ≤ 2 * (((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card : ℝ) := h2
    _ = 2 * ((↑(unitLattice K) ∩ unitBox K Y).ncard : ℝ) := by rw [himgcard]
    _ ≤ 2 * (5 * (5 * Y + 1) ^ (d - 1)) := by linarith
    _ = 10 * (5 * Y + 1) ^ (d - 1) := by ring
end SumProduct
