-- Prove2me | solution 1 for SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_6_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T18:34:37.809858+00:00
-- url     : https://prove2.me/submissions/c98888e0-3779-4578-8553-da4966f2cb5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Branching
import Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_6_4
import Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_6_5

set_option autoImplicit false
open scoped Classical
noncomputable section

open SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem solution (K : Type) [Field K] [CharZero K] : symVBP K = symVS K :=
  Set.Subset.antisymm (lemma_6_4 K) (lemma_6_5 K)
