-- Prove2me | solution 1 for Research.arbitrarily_large_global_shell_six_counterexamples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:22.121659+00:00
-- url     : https://prove2.me/submissions/6796c797-bb21-4893-856f-5cb30732263b

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_triCoordsWithinThirtySix_card
public import Theorems.Thm_Research_obliqueBlocks_oneSeparated
public import Theorems.Thm_Research_obliqueBlocks_global_normalized_excess
public import Theorems.Thm_Research_obliqueBlocks_unordered_normalized_excess

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (N : ℕ) :
    N ≤ Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) ∧
    (∀ q s : Fin (N + 1) × (Fin 365 × Fin 365), q ≠ s →
      1 ≤ sqDist (obliqueBlocks (N + 1) q) (obliqueBlocks (N + 1) s)) ∧
    triCoordsWithinThirtySix.card = 126 ∧
    126 * Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) <
      (radiusSixDirectedPairs (obliqueBlocks (N + 1))).card ∧
    63 * Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) <
      (radiusSixOrderedPairs (obliqueBlocks (N + 1))).card := by
  refine ⟨?_, obliqueBlocks_oneSeparated (N + 1),
    triCoordsWithinThirtySix_card,
    obliqueBlocks_global_normalized_excess (N + 1) (by omega),
    obliqueBlocks_unordered_normalized_excess (N + 1) (by omega)⟩
  simp only [Fintype.card_prod, Fintype.card_fin]
  nlinarith
end Research
