-- Prove2me | solution 1 for Research.obliqueBlocks_unordered_normalized_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:28:27.847371+00:00
-- url     : https://prove2.me/submissions/241f8425-0a12-4176-ae68-cfe07b5101b0

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_obliqueBlocks_ordered_card_ge

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m : ℕ) (hm : 0 < m) :
    63 * Fintype.card (Fin m × (Fin 365 × Fin 365)) <
      (radiusSixOrderedPairs (obliqueBlocks m)).card := by
  have hlower := obliqueBlocks_ordered_card_ge m
  calc
    63 * Fintype.card (Fin m × (Fin 365 × Fin 365)) =
        m * 8393175 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      ring
    _ < m * 8393309 :=
      Nat.mul_lt_mul_of_pos_left (by norm_num) hm
    _ ≤ (radiusSixOrderedPairs (obliqueBlocks m)).card := hlower
end Research
