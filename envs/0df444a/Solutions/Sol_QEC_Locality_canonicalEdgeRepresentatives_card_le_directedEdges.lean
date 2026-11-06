-- Prove2me | solution 1 for QEC.Locality.canonicalEdgeRepresentatives_card_le_directedEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:23:46.34621+00:00
-- url     : https://prove2.me/submissions/176dc043-ef06-48df-9cf1-c47685d3dc06

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision

set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) :
    (canonicalEdgeRepresentatives G).card ≤ (directedEdgeFinset G).card := by
  classical
  exact Finset.card_image_le
end QEC.Locality
