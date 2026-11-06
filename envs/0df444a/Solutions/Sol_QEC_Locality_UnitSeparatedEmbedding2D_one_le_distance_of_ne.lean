-- Prove2me | solution 1 for QEC.Locality.UnitSeparatedEmbedding2D.one_le_distance_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:32:54.886347+00:00
-- url     : https://prove2.me/submissions/30411ab9-4a54-42bf-8c4d-f90e7906336c

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC
open QEC.Locality
open QEC.Locality.UnitSeparatedEmbedding2D
variable {ι : Type*}
namespace QEC.Locality.UnitSeparatedEmbedding2D
theorem _root_.solution (embedding : UnitSeparatedEmbedding2D ι)
    {p q : ι} (hpq : p ≠ q) :
    1 ≤ embedding.distance p q :=
  embedding.unitSeparated hpq
end QEC.Locality.UnitSeparatedEmbedding2D
