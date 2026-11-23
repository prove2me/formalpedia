-- Prove2me | solution 1 for SumProduct.mem_convexBodyLT_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:50:39.669959+00:00
-- url     : https://prove2.me/submissions/8d289c8d-5c52-448c-bd73-c4203cf4d34d

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
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Metric
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (f : InfinitePlace K → NNReal)
    (y : mixedSpace K) : y ∈ convexBodyLT K f ↔ ∀ w : InfinitePlace K, normAtPlace w y < f w := by
  simp only [convexBodyLT, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_ball_zero_iff, Subtype.forall]
  constructor
  · rintro ⟨h1, h2⟩ w
    rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 w hw
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 w hw
  · intro h
    exact ⟨fun w hw => by rw [← normAtPlace_apply_of_isReal hw]; exact h w,
           fun w hw => by rw [← normAtPlace_apply_of_isComplex hw]; exact h w⟩
end SumProduct
