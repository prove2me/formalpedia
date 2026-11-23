-- Prove2me | solution 1 for SumProduct.lattice_count_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:56:33.236165+00:00
-- url     : https://prove2.me/submissions/8d599ea0-69f5-44a3-9b8b-374799367015

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_boxAdd_card_le
import Theorems.Thm_SumProduct_boxAdd_card_ge

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    X ^ d / Real.sqrt |(NumberField.discr K : ℝ)| ≤ (boxAdd K X).card ∧
      ((boxAdd K X).card : ℝ) ≤ (2 * X + 1) ^ d :=
  ⟨boxAdd_card_ge hd X hX, boxAdd_card_le K d hd X hX⟩
end SumProduct
