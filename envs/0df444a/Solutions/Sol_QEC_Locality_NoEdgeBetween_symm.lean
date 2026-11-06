-- Prove2me | solution 1 for QEC.Locality.NoEdgeBetween.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:05:33.029204+00:00
-- url     : https://prove2.me/submissions/a25ff5a0-efe0-4cb0-acef-1e5baaca4d2f

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace NoEdgeBetween
theorem _root_.solution {G : ConnectivityGraph ι} {left right : Finset ι}
    (h : NoEdgeBetween G left right) : NoEdgeBetween G right left := by
  intro y hy x hx hxy
  exact h hx hy (G.symmetric hxy)
end NoEdgeBetween
end QEC.Locality
