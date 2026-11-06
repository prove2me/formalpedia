-- Prove2me | solution 1 for QEC.Locality.NoEdgeBetween.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:13:09.513202+00:00
-- url     : https://prove2.me/submissions/7eba02e9-059f-4c16-b528-1c7f3c6e8206

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
theorem _root_.solution {G : ConnectivityGraph ι}
    {left right left' right' : Finset ι}
    (h : NoEdgeBetween G left right) (hleft : left' ⊆ left) (hright : right' ⊆ right) :
    NoEdgeBetween G left' right' := by
  intro x hx y hy
  exact h (hleft hx) (hright hy)
end NoEdgeBetween
end QEC.Locality
