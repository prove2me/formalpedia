-- Prove2me | solution 1 for Research.not_eventualShellSixDirectedAverageBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:28:18.12+00:00
-- url     : https://prove2.me/submissions/8f83c2c0-6025-46f3-9a63-ffbd5c37ec83

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_radiusSixOrdinaryDirectedPairs_eq
public import Theorems.Thm_Research_obliqueBlocks_global_normalized_excess
public import Theorems.Thm_Research_obliqueBlocks_ordinaryOneSeparated

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    ¬ EventualShellSixDirectedAverageBound := by
  rintro ⟨N, hN⟩
  have hcard : N ≤
      Fintype.card (Fin (N + 1) × (Fin 365 × Fin 365)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  have hu := hN (Fin (N + 1) × (Fin 365 × Fin 365)) hcard
    (obliqueBlocks (N + 1)) (obliqueBlocks_ordinaryOneSeparated (N + 1))
  rw [radiusSixOrdinaryDirectedPairs_eq] at hu
  have hl := obliqueBlocks_global_normalized_excess (N + 1) (by omega)
  omega
end Research
