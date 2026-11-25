-- Prove2me | solution 1 for Research.arbitrarily_large_global_shell_six_counterexamples_ordinary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:33:09.903713+00:00
-- url     : https://prove2.me/submissions/eea35a29-15fa-421b-8f67-b6b76de8d697

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_radiusSixOrdinaryDirectedPairs_eq
public import Theorems.Thm_Research_radiusSixOrdinaryOrderedPairs_eq
public import Theorems.Thm_Research_arbitrarily_large_global_shell_six_counterexamples
public import Theorems.Thm_Research_obliqueBlocks_ordinaryOneSeparated

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (N : ℕ) :
    N ≤ Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) ∧
    OrdinaryOneSeparatedOn (obliqueBlocks (N + 1)) ∧
    triCoordsWithinThirtySix.card = 126 ∧
    126 * Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) <
      (radiusSixOrdinaryDirectedPairs (obliqueBlocks (N + 1))).card ∧
    63 * Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) <
      (radiusSixOrdinaryOrderedPairs (obliqueBlocks (N + 1))).card := by
  have h := arbitrarily_large_global_shell_six_counterexamples N
  refine ⟨h.1, obliqueBlocks_ordinaryOneSeparated (N + 1), h.2.2.1, ?_, ?_⟩
  · rw [radiusSixOrdinaryDirectedPairs_eq]
    exact h.2.2.2.1
  · rw [radiusSixOrdinaryOrderedPairs_eq]
    exact h.2.2.2.2
end Research
