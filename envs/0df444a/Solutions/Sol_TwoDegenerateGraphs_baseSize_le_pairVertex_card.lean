-- Prove2me | solution 1 for TwoDegenerateGraphs.baseSize_le_pairVertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/f3a36a12-1a47-4f8f-98f2-c451670790ad

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (baseSize depth : ℕ) :
    baseSize ≤ Fintype.card (PairVertex baseSize depth) := by
  calc
    baseSize = Fintype.card (PairLayer baseSize 0) :=
      (pairLayer_card_zero baseSize).symm
    _ ≤ Fintype.card (PairVertex baseSize depth) :=
      Fintype.card_le_of_embedding
        (pairLayerEmbedding baseSize depth 0 (by omega))
end TwoDegenerateGraphs
