-- Prove2me | solution 1 for Research.obliquePatch_unordered_normalized_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:25:16.653197+00:00
-- url     : https://prove2.me/submissions/2b497a82-47e9-4de6-8be8-5b92418fdbca

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_obliquePatch_ordered_card_ge

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    63 * Fintype.card (Fin 365 × Fin 365) <
      (radiusSixOrderedPairs obliquePoint).card := by
  have h := obliquePatch_ordered_card_ge
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num
  omega
end Research
