-- Prove2me | solution 1 for SumProduct.normAtPlace_latticeEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:50:39.166684+00:00
-- url     : https://prove2.me/submissions/31495725-0e68-4f6b-b1fd-3e162183823f

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_latticeEmbed_apply
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult


attribute [local simp] SumProduct.latticeEmbed_apply

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (α : 𝓞 K)
    (w : InfinitePlace K) : normAtPlace w (latticeEmbed K α) = w (α : K) := by
  rw [latticeEmbed_apply, normAtPlace_apply]
end SumProduct
