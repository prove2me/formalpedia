-- Prove2me | solution 2 for QEC.Locality.inducedSubgraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:27:31.903304+00:00
-- url     : https://prove2.me/submissions/92079595-a740-41ff-b58e-69f06f14946a

import Mathlib
import Definitions.Def_QEC_Locality_Graph_Core
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (x y : {i : ι // i ∈ vertices}) :
    (inducedSubgraph G vertices).adjacent x y ↔ G.adjacent x.1 y.1 := Iff.rfl
