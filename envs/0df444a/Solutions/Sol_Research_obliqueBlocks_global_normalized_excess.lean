-- Prove2me | solution 1 for Research.obliqueBlocks_global_normalized_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:23:45.564018+00:00
-- url     : https://prove2.me/submissions/3a6154cf-9a2c-4f5f-9f58-abfc31da4166

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_obliqueBlocks_directed_card_ge

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m : ℕ) (hm : 0 < m) :
    126 * Fintype.card (Fin m × (Fin 365 × Fin 365)) <
      (radiusSixDirectedPairs (obliqueBlocks m)).card := by
  have hlower := obliqueBlocks_directed_card_ge m
  calc
    126 * Fintype.card (Fin m × (Fin 365 × Fin 365)) =
        m * 16786350 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      ring
    _ < m * 16786618 :=
      Nat.mul_lt_mul_of_pos_left (by norm_num) hm
    _ ≤ (radiusSixDirectedPairs (obliqueBlocks m)).card := hlower
end Research
