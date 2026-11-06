-- Prove2me | solution 1 for QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:16:39.79859+00:00
-- url     : https://prove2.me/submissions/0148fd81-11c3-4d39-ade8-421a20b01a39

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace MarkedSeparatorSpine
theorem _root_.solution
    {G : ConnectivityGraph ι} {marked vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
    (hminimum : separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
    (hleftLight : 3 * (marked ∩ left).card ≤ 2 * marked.card)
    (hrightLight : 3 * (marked ∩ right).card ≤ 2 * marked.card) :
    (MarkedSeparatorSpine.stop hpartition hminimum hleftLight hrightLight).exposedSide = ∅ := rfl
end MarkedSeparatorSpine
end QEC.Locality
