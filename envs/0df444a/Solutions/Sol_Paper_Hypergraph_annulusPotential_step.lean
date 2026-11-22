-- Prove2me | solution 1 for Paper.Hypergraph.annulusPotential_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:53.43117+00:00
-- url     : https://prove2.me/submissions/363096ec-556f-47e1-b8cc-f8a7497ebc50

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {a b q du dv z : ℝ}
    (hgap : 0 < b - a - q) (hz : 0 ≤ z) (hzq : z ≤ q) (hd : dv ≤ du + z) :
    annulusPotential a b q dv ≤ annulusPotential a b q du +
      if a < dv ∧ dv ≤ b then z else 0 := by
  by_cases ha : a < dv <;> by_cases hb : dv ≤ b <;>
    simp only [ha, hb, and_self, and_true, and_false, false_and, if_true, if_false,
      annulusPotential, min_def, max_def] <;>
    split_ifs <;> linarith
end Paper.Hypergraph
