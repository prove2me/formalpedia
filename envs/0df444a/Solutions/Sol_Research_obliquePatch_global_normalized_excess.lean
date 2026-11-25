-- Prove2me | solution 1 for Research.obliquePatch_global_normalized_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:19:11.843041+00:00
-- url     : https://prove2.me/submissions/3bbb4b06-85c6-40e5-bf2d-4a7df26dc0b7

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_obliquePatch_directed_card_ge

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    126 * Fintype.card (Fin 365 × Fin 365) <
      (radiusSixDirectedPairs obliquePoint).card := by
  have h := obliquePatch_directed_card_ge
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num
  omega
end Research
