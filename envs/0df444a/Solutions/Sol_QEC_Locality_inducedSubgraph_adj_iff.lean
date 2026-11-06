-- Prove2me | solution 1 for QEC.Locality.inducedSubgraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:38.041175+00:00
-- url     : https://prove2.me/submissions/1771999f-3143-40b1-88d6-69aea6369524

import Mathlib
import Definitions.Def_QEC_Locality_Graph_Core

set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (x y : {i : ι // i ∈ vertices}) :
    (inducedSubgraph G vertices).adjacent x y ↔ G.adjacent x.1 y.1 :=
  Iff.rfl
end QEC.Locality
