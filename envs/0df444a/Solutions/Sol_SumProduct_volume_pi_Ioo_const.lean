-- Prove2me | solution 1 for SumProduct.volume_pi_Ioo_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:06:39.508994+00:00
-- url     : https://prove2.me/submissions/55b9b331-0032-4c8b-a3e1-4c57611de483

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_card_infinitePlace_eq
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open MeasureTheory NumberField NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) {a b : ℝ} (hab : a ≤ b) :
    volume (Set.univ.pi fun _ : InfinitePlace K => Set.Ioo a b) = ENNReal.ofReal ((b - a) ^ d) := by
  rw [volume_pi_pi]
  simp only [Real.volume_Ioo]
  rw [Finset.prod_const, Finset.card_univ, card_infinitePlace_eq hd,
    ← ENNReal.ofReal_pow (by linarith)]
end SumProduct
