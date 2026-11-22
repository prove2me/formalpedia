-- Prove2me | solution 1 for Paper.Hypergraph.independent_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:53.380632+00:00
-- url     : https://prove2.me/submissions/02c499b6-52cd-4a88-9085-15465e3958d9

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {S : Finset ℕ}
    (hS : S ⊆ H.vertices) (hi : H.independent S) : S.card ≤ H.independenceNumber :=
  Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hS, hi⟩)
end Paper.Hypergraph
