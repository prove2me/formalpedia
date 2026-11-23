-- Prove2me | solution 1 for SumProduct.tsum_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:21.352698+00:00
-- url     : https://prove2.me/submissions/eef56cec-bded-4ed4-ae20-23d5b391d83e

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_latticeEmbed_apply
import Theorems.Thm_SumProduct_latticeEquiv_coe
import Theorems.Thm_SumProduct_count_encard_le
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult


attribute [local simp] SumProduct.latticeEmbed_apply
attribute [local simp] SumProduct.latticeEquiv_coe

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    ∑' l : ↥(mixedEmbedding.integerLattice K),
        (convexBodyLT K (fun _ => r)).indicator (fun _ => (1 : ENNReal)) ((l : mixedSpace K) + x)
      ≤ ((boxAdd K (2 * (r : ℝ))).card : ENNReal) := by
  have hfun : (fun α : 𝓞 K =>
        (convexBodyLT K (fun _ => r)).indicator (fun _ => (1 : ENNReal)) (latticeEmbed K α + x))
      = {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.indicator (fun _ => 1) := by
    funext α
    by_cases h : latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)
    · have h' : α ∈ {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : α ∉ {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  rw [← Equiv.tsum_eq (latticeEquiv K)]
  simp only [latticeEquiv_coe]
  rw [hfun, ← tsum_subtype, ENNReal.tsum_set_one]
  exact_mod_cast count_encard_le x r
end SumProduct
